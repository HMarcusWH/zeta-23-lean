import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Zeta23.OPICA.LocallyFiniteSignedMeasure
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# The two explicit tests in the signed separator

The normalization is `sin (π*x)/(π*x)` with value one at zero.
The exact Fourier pair is proved through box convolution and Fourier inversion.
Compact smooth convolution regularizations provide legitimate Schwartz tests
with the actual sinc-squared majorant for signed-measure limits.
-/

noncomputable section

namespace Zeta23.OPICA

open Set MeasureTheory
open scoped FourierTransform Convolution ContDiff

def sincSquared (x : ℝ) : ℝ := Real.sinc (Real.pi * x) ^ 2

def unitTriangle (x : ℝ) : ℝ := max (1 - |x|) 0

theorem sincSquared_zero : sincSquared 0 = 1 := by
  norm_num [sincSquared]

theorem sincSquared_nonneg (x : ℝ) : 0 ≤ sincSquared x := by
  exact sq_nonneg _

theorem sincSquared_le_one (x : ℝ) : sincSquared x ≤ 1 := by
  have h := abs_le.mp (Real.abs_sinc_le_one (Real.pi * x))
  unfold sincSquared
  nlinarith [sq_nonneg (Real.sinc (Real.pi * x) - 1),
    sq_nonneg (Real.sinc (Real.pi * x) + 1)]

theorem sincSquared_even (x : ℝ) : sincSquared (-x) = sincSquared x := by
  simp [sincSquared, Real.sinc_neg]

theorem sincSquared_continuous : Continuous sincSquared := by
  exact (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2

theorem sincSquared_int_zero {n : ℤ} (hn : n ≠ 0) : sincSquared (n : ℝ) = 0 := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [sincSquared, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hnreal),
    mul_comm Real.pi, Real.sin_int_mul_pi]
  simp

theorem sincSquared_pos_off_lattice {x : ℝ}
    (hx : ¬ ∃ n : ℤ, (n : ℝ) = x) : 0 < sincSquared x := by
  have hxzero : x ≠ 0 := by
    intro h
    exact hx ⟨0, by simpa using h.symm⟩
  have hsine : Real.sin (Real.pi * x) ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    apply hx
    refine ⟨n, ?_⟩
    apply (mul_left_cancel₀ Real.pi_ne_zero)
    simpa only [mul_comm Real.pi] using hn
  unfold sincSquared
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hxzero)]
  exact sq_pos_of_ne_zero (div_ne_zero hsine (mul_ne_zero Real.pi_ne_zero hxzero))

theorem sincSquared_mul_sq_le_one (x : ℝ) : sincSquared x * x ^ 2 ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have hid : sincSquared x * x ^ 2 * Real.pi ^ 2 = Real.sin (Real.pi * x) ^ 2 := by
    rw [sincSquared, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx), div_pow]
    field_simp
  have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have hnonneg : 0 ≤ sincSquared x * x ^ 2 :=
    mul_nonneg (sincSquared_nonneg x) (sq_nonneg x)
  have hsin : Real.sin (Real.pi * x) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x), sq_nonneg (Real.cos (Real.pi * x))]
  nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hpi)]

/-- A uniform integrable majorant for linearly growing measures. -/
theorem sincSquared_le_quadraticDecay (x : ℝ) : sincSquared x ≤ 4 * quadraticDecay x := by
  have hs : 0 ≤ sincSquared x := sincSquared_nonneg x
  have hsq : (1 + |x|) ^ 2 ≤ 2 + 2 * x ^ 2 := by
    nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have hbound := mul_le_mul_of_nonneg_left hsq hs
  have hlast : sincSquared x * (1 + |x|) ^ 2 ≤ 4 := by
    nlinarith [sincSquared_le_one x, sincSquared_mul_sq_le_one x]
  unfold quadraticDecay
  simpa only [mul_one_div] using
    (le_div_iff₀ (by positivity : 0 < (1 + |x|) ^ 2)).mpr hlast

theorem sincSquared_integrable_of_linear_growth (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsLocallyFiniteMeasure μ] (hμ : LinearMassGrowth μ) :
    MeasureTheory.Integrable sincSquared μ := by
  apply ((quadraticDecay_integrable_of_linear_growth μ hμ).const_mul 4).mono'
    sincSquared_continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (sincSquared_nonneg x)]
    exact sincSquared_le_quadraticDecay x

theorem unitTriangle_nonneg (x : ℝ) : 0 ≤ unitTriangle x := le_max_right _ _

theorem unitTriangle_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) :
    unitTriangle x = 0 := by
  exact max_eq_right (sub_nonpos.mpr hx)

theorem unitTriangle_zero : unitTriangle 0 = 1 := by norm_num [unitTriangle]

theorem unitTriangle_even (x : ℝ) : unitTriangle (-x) = unitTriangle x := by
  simp [unitTriangle]

theorem unitTriangle_continuous : Continuous unitTriangle :=
  (continuous_const.sub continuous_abs).max continuous_const

/-- The closed unit box. Endpoint choices do not affect its Fourier integral. -/
def unitBox (x : ℝ) : ℂ := (Icc (-(1/2 : ℝ)) (1/2 : ℝ)).indicator (fun _ => 1) x

theorem unitBox_integrable : Integrable unitBox := by
  unfold unitBox
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact integrableOn_const (by simp : volume (Icc (-(1/2 : ℝ)) (1/2 : ℝ)) ≠ ⊤)

theorem unitBox_fourier (xi : ℝ) : 𝓕 unitBox xi = (Real.sinc (Real.pi*xi) : ℂ) := by
  have hc := integral_charFun_Icc (μ := Measure.dirac (-2*Real.pi*xi))
    (r := (1/2 : ℝ)) (by norm_num)
  have harg : (1/2 : ℝ)*(-2*Real.pi*xi) = -(Real.pi*xi) := by ring
  have hkernel (t : ℝ) : Complex.exp ((-2*Real.pi*t*xi : ℝ)*Complex.I) =
      charFun (Measure.dirac (-2*Real.pi*xi)) t := by
    simp only [charFun_apply_real, integral_dirac]
    congr 1
    norm_cast
    ring
  have hbox : (fun t : ℝ => Complex.exp ((-2*Real.pi*t*xi : ℝ)*Complex.I) • unitBox t) =
      (Icc (-(1/2 : ℝ)) (1/2 : ℝ)).indicator
        (fun t => charFun (Measure.dirac (-2*Real.pi*xi)) t) := by
    funext t
    by_cases ht : t ∈ Icc (-(1/2 : ℝ)) (1/2 : ℝ)
    · simp only [unitBox, indicator_of_mem ht, smul_eq_mul, mul_one, hkernel]
    · simp only [unitBox, indicator_of_notMem ht, smul_zero]
  rw [Real.fourier_real_eq_integral_exp_smul, hbox, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : -(1/2 : ℝ) ≤ 1/2)]
  have harg2 : (2 : ℝ)⁻¹ * (2*Real.pi*xi) = Real.pi*xi := by ring
  simpa [harg, harg2, Real.sinc_neg] using hc

theorem unitBox_convolution (x : ℝ) :
    (unitBox ⋆[ContinuousLinearMap.mul ℂ ℂ] unitBox) x = (unitTriangle x : ℂ) := by
  let J := Icc (max (-(1/2 : ℝ)) (x-1/2)) (min (1/2 : ℝ) (x+1/2))
  have hmem (t : ℝ) :
      (t ∈ Icc (-(1/2 : ℝ)) (1/2 : ℝ) ∧ x-t ∈ Icc (-(1/2 : ℝ)) (1/2 : ℝ)) ↔ t ∈ J := by
    dsimp [J]
    simp only [mem_Icc, max_le_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
      exact ⟨⟨h1,by linarith⟩,⟨h2,by linarith⟩⟩
    · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
      exact ⟨⟨h1,h3⟩,⟨by linarith,by linarith⟩⟩
  have hintegrand : (fun t => unitBox t * unitBox (x-t)) = J.indicator (fun _ => (1 : ℂ)) := by
    funext t
    by_cases h1 : t ∈ Icc (-(1/2 : ℝ)) (1/2 : ℝ)
    · by_cases h2 : x-t ∈ Icc (-(1/2 : ℝ)) (1/2 : ℝ)
      · have h3 := (hmem t).mp ⟨h1,h2⟩
        simp only [unitBox, indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem h3, mul_one]
      · have h3 : t ∉ J := fun h => h2 ((hmem t).mpr h).2
        simp only [unitBox, indicator_of_mem h1, indicator_of_notMem h2, indicator_of_notMem h3, mul_zero]
    · have h3 : t ∉ J := fun h => h1 ((hmem t).mpr h).1
      simp only [unitBox, indicator_of_notMem h1, indicator_of_notMem h3, zero_mul]
  have hlength : max (min (1/2 : ℝ) (x+1/2) - max (-(1/2 : ℝ)) (x-1/2)) 0 = unitTriangle x := by
    unfold unitTriangle
    by_cases hx : 0 ≤ x
    · rw [min_eq_left (show (1/2 : ℝ) ≤ x+1/2 by linarith),
        max_eq_right (show -(1/2 : ℝ) ≤ x-1/2 by linarith), abs_of_nonneg hx]
      congr 1
      ring
    · have hx' := le_of_not_ge hx
      rw [min_eq_right (show x+1/2 ≤ (1/2 : ℝ) by linarith),
        max_eq_left (show x-1/2 ≤ -(1/2 : ℝ) by linarith), abs_of_nonpos hx']
      congr 1
      ring
  rw [convolution_def]
  change (∫ t : ℝ, unitBox t * unitBox (x-t)) = _
  rw [hintegrand, integral_indicator measurableSet_Icc, integral_const]
  simp only [measureReal_restrict_apply_univ, Complex.real_smul, mul_one]
  change (volume.real J : ℂ) = (unitTriangle x : ℂ)
  rw [show volume.real J = unitTriangle x by dsimp [J]; rw [Real.volume_real_Icc, hlength]]

theorem unitTriangle_fourier (xi : ℝ) :
    𝓕 (fun x => (unitTriangle x : ℂ)) xi = (sincSquared xi : ℂ) := by
  have heq : (fun x => (unitTriangle x : ℂ)) = unitBox ⋆[ContinuousLinearMap.mul ℂ ℂ] unitBox := by
    funext x
    exact (unitBox_convolution x).symm
  rw [heq, Real.fourier_mul_convolution_eq unitBox_integrable unitBox_integrable,
    unitBox_fourier]
  simp only [sincSquared, pow_two, Complex.ofReal_mul]

theorem sincSquared_volume_integrable : Integrable sincSquared := by
  apply sincSquared_integrable_of_linear_growth
  refine ⟨2, by norm_num, ?_⟩
  intro R hR
  rw [Real.volume_real_Icc, max_eq_left (by linarith)]
  linarith

theorem unitTriangle_volume_integrable : Integrable (fun x => (unitTriangle x : ℂ)) := by
  have heq : (fun x => (unitTriangle x : ℂ)) = unitBox ⋆[ContinuousLinearMap.mul ℂ ℂ] unitBox := by
    funext x
    exact (unitBox_convolution x).symm
  rw [heq]
  exact unitBox_integrable.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) unitBox_integrable

/-- The exact sinc-squared/triangle Fourier pair in the paper's 2π convention. -/
theorem sincSquared_fourier (xi : ℝ) :
    𝓕 (fun x => (sincSquared x : ℂ)) xi = (unitTriangle xi : ℂ) := by
  have heq : 𝓕 (fun x => (unitTriangle x : ℂ)) = fun x => (sincSquared x : ℂ) :=
    funext unitTriangle_fourier
  have hc : Continuous (fun x => (unitTriangle x : ℂ)) :=
    Complex.continuous_ofReal.comp unitTriangle_continuous
  have hi : Integrable (𝓕 (fun x => (unitTriangle x : ℂ))) := by
    rw [heq]
    exact sincSquared_volume_integrable.ofReal
  have hinv := hc.fourierInv_fourier_eq unitTriangle_volume_integrable hi
  rw [heq] at hinv
  have h := congrFun hinv (-xi)
  rw [Real.fourierInv_eq_fourier_neg, neg_neg, unitTriangle_even] at h
  exact h


/-- The genuine compactly supported triangle has no Schwartz smoothness claim. -/
theorem unitTriangle_hasCompactSupport : HasCompactSupport (fun x => (unitTriangle x : ℂ)) := by
  have hs : Function.support (fun x => (unitTriangle x : ℂ)) ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    change (unitTriangle x : ℂ) ≠ 0 at hx
    by_contra h
    have ha : 1 ≤ |x| := by
      simp only [mem_Icc, not_and_or, not_le] at h
      rcases h with h | h
      · rw [abs_of_neg (by linarith : x < 0)]
        linarith
      · exact le_trans (by linarith) (le_abs_self x)
    exact hx (by rw [unitTriangle_eq_zero_of_one_le_abs ha]; rfl)
  exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)

def normalizedComplexBump (φ : ContDiffBump (0 : ℝ)) (x : ℝ) : ℂ := φ.normed volume x

theorem normalizedComplexBump_integrable (φ : ContDiffBump (0 : ℝ)) :
    Integrable (normalizedComplexBump φ) := φ.integrable_normed.ofReal

theorem normalizedComplexBump_compact (φ : ContDiffBump (0 : ℝ)) :
    HasCompactSupport (normalizedComplexBump φ) := φ.hasCompactSupport_normed.comp_left rfl

theorem normalizedComplexBump_smooth (φ : ContDiffBump (0 : ℝ)) :
    ContDiff ℝ ∞ (normalizedComplexBump φ) := by
  exact Complex.ofRealCLM.contDiff.comp φ.contDiff_normed

/-- A compact smooth regularization used for distributional pairing. -/
def regularizedTriangle (φ : ContDiffBump (0 : ℝ)) : SchwartzMap ℝ ℂ :=
  (normalizedComplexBump_compact φ |>.convolution unitTriangle_hasCompactSupport
    (L := ContinuousLinearMap.mul ℂ ℂ)).toSchwartzMap
    ((normalizedComplexBump_compact φ).contDiff_convolution_left
      (ContinuousLinearMap.mul ℝ ℂ) (normalizedComplexBump_smooth φ)
      unitTriangle_volume_integrable.locallyIntegrable)

theorem regularizedTriangle_fourier (φ : ContDiffBump (0 : ℝ)) (xi : ℝ) :
    𝓕 (regularizedTriangle φ : ℝ → ℂ) xi =
      𝓕 (normalizedComplexBump φ) xi * (sincSquared xi : ℂ) := by
  change 𝓕 (normalizedComplexBump φ ⋆[ContinuousLinearMap.mul ℂ ℂ]
    (fun x => (unitTriangle x : ℂ))) xi = _
  rw [Real.fourier_mul_convolution_eq (normalizedComplexBump_integrable φ)
    unitTriangle_volume_integrable, unitTriangle_fourier]

theorem normalizedComplexBump_fourier_norm_le (φ : ContDiffBump (0 : ℝ)) (xi : ℝ) :
    ‖𝓕 (normalizedComplexBump φ) xi‖ ≤ 1 := by
  rw [Real.fourier_eq]
  calc
    _ ≤ ∫ x : ℝ, ‖Real.fourierChar (-inner ℝ x xi) • normalizedComplexBump φ x‖ :=
      norm_integral_le_integral_norm _
    _ = 1 := by
      simp_rw [Circle.norm_smul, normalizedComplexBump, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed _)]
      exact φ.integral_normed

theorem regularizedTriangle_fourier_norm_le (φ : ContDiffBump (0 : ℝ)) (xi : ℝ) :
    ‖𝓕 (regularizedTriangle φ : ℝ → ℂ) xi‖ ≤ sincSquared xi := by
  rw [regularizedTriangle_fourier, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sincSquared_nonneg xi)]
  exact mul_le_of_le_one_left (sincSquared_nonneg xi)
    (normalizedComplexBump_fourier_norm_le φ xi)

end Zeta23.OPICA

#print axioms Zeta23.OPICA.sincSquared_pos_off_lattice
