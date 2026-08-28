import Zeta23.CCM.DictionaryTentMollifier
import Zeta23.CCM.DictionaryTentDecay
import Zeta23.Poisson.PaperFTConvolution

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter ContinuousLinearMap
open scoped Convolution Topology

/-!
# Transform factorization and strip control for the mollified dictionary tent

This module is the M2 architecture gate.  It connects the real normalized-bump
convolution used for physical-space approximation to a complex convolution,
then applies the neutral complex-frequency `paperFT` convolution theorem.

No explicit-formula limit passage is performed here.
-/

/-- Complexification of the canonical real normalized mollifier. -/
def dictionaryTentMollifierComplex (n : ℕ) : ℝ → ℂ :=
  fun x => (dictionaryTentMollifier n x : ℂ)

/-- Native `paperFT` transform of the canonical mollifier. -/
def dictionaryTentMollifierTransform (n : ℕ) (z : ℂ) : ℂ :=
  Zeta23.paperFT (dictionaryTentMollifierComplex n) z

/-- The real-convolution definition of the mollified tent is exactly the
corresponding complex convolution after complexification. -/
theorem dictionaryTentMollified_eq_complexConvolution
    (L : ℝ) (n : ℕ) :
    dictionaryTentMollified L n =
      dictionaryTentMollifierComplex n ⋆[mul ℂ ℂ, volume] dictionaryTent L := by
  funext x
  change
    (((∫ t : ℝ,
        dictionaryTentMollifier n t * dictionaryApertureCoord L (x - t)) : ℝ) : ℂ) =
      ∫ t : ℝ,
        dictionaryTentMollifierComplex n t * dictionaryTent L (x - t)
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  simp [dictionaryTentMollifierComplex, dictionaryTent]

/-- The complex mollifier is continuous. -/
theorem continuous_dictionaryTentMollifierComplex (n : ℕ) :
    Continuous (dictionaryTentMollifierComplex n) := by
  exact Complex.ofRealCLM.continuous.comp
    (contDiff_dictionaryTentMollifier n 0).continuous

/-- The complex mollifier has compact support. -/
theorem dictionaryTentMollifierComplex_hasCompactSupport (n : ℕ) :
    HasCompactSupport (dictionaryTentMollifierComplex n) := by
  exact (dictionaryTentMollifier_hasCompactSupport n).comp_left
    (g := Complex.ofReal) Complex.ofReal_zero

/-- The complex mollifier is integrable. -/
theorem integrable_dictionaryTentMollifierComplex (n : ℕ) :
    Integrable (dictionaryTentMollifierComplex n) :=
  (continuous_dictionaryTentMollifierComplex n).integrable_of_hasCompactSupport
    (dictionaryTentMollifierComplex_hasCompactSupport n)

/-- Every canonical mollifier radius is at most one. -/
theorem dictionaryTentMollifierRadius_le_one (n : ℕ) :
    dictionaryTentMollifierRadius n ≤ 1 := by
  rw [dictionaryTentMollifierRadius, div_le_one (by positivity)]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- Uniform physical support bound for the complex mollifier. -/
theorem dictionaryTentMollifierComplex_support_abs_le_one
    (n : ℕ) {x : ℝ}
    (hx : dictionaryTentMollifierComplex n x ≠ 0) :
    |x| ≤ 1 := by
  have hxreal : dictionaryTentMollifier n x ≠ 0 := by
    intro hzero
    apply hx
    simp [dictionaryTentMollifierComplex, hzero]
  have hxball :
      x ∈ Metric.ball (0 : ℝ) (dictionaryTentMollifierBump n).rOut := by
    rw [← (dictionaryTentMollifierBump n).support_normed_eq (μ := volume)]
    exact hxreal
  have habslt : |x| < dictionaryTentMollifierRadius n := by
    simpa [Real.dist_eq, dictionaryTentMollifierBump_rOut] using hxball
  exact habslt.le.trans (dictionaryTentMollifierRadius_le_one n)

/-- The L1 norm of the nonnegative normalized complex mollifier is exactly one. -/
theorem integral_norm_dictionaryTentMollifierComplex (n : ℕ) :
    (∫ x : ℝ, ‖dictionaryTentMollifierComplex n x‖) = 1 := by
  have heq :
      (fun x : ℝ => ‖dictionaryTentMollifierComplex n x‖) =
        dictionaryTentMollifier n := by
    funext x
    have hnonneg :
        0 ≤ dictionaryTentMollifier n x := by
      exact (dictionaryTentMollifierBump n).nonneg_normed (μ := volume) x
    simp [dictionaryTentMollifierComplex, hnonneg]
  rw [heq]
  exact (dictionaryTentMollifierBump n).integral_normed (μ := volume)

/-- M2: exact complex-frequency factorization of the mollified tent transform. -/
theorem paperFT_dictionaryTentMollified_factor
    {L : ℝ} (hL : 0 < L) (n : ℕ) (z : ℂ) :
    Zeta23.paperFT (dictionaryTentMollified L n) z =
      dictionaryTentMollifierTransform n z *
        Zeta23.paperFT (dictionaryTent L) z := by
  rw [dictionaryTentMollified_eq_complexConvolution]
  exact Zeta23.paperFT_mul_convolution_eq_of_continuous_compactSupport
    (continuous_dictionaryTentMollifierComplex n)
    (dictionaryTentMollifierComplex_hasCompactSupport n)
    (continuous_dictionaryTent L)
    (dictionaryTent_hasCompactSupport hL)
    z

/-- The mollifier transform is uniformly bounded on the critical strip,
independently of the mollification index. -/
theorem norm_dictionaryTentMollifierTransform_le_exp_half
    (n : ℕ) {z : ℂ} (hstrip : |z.im| ≤ 1 / 2) :
    ‖dictionaryTentMollifierTransform n z‖ ≤ Real.exp (1 / 2) := by
  have hbase := Zeta23.norm_paperFT_le
    (integrable_dictionaryTentMollifierComplex n)
    (fun x hx => dictionaryTentMollifierComplex_support_abs_le_one n hx)
    z
  rw [integral_norm_dictionaryTentMollifierComplex] at hbase
  calc
    ‖dictionaryTentMollifierTransform n z‖
        ≤ Real.exp (|z.im| * 1) * 1 := by
          simpa [dictionaryTentMollifierTransform] using hbase
    _ = Real.exp |z.im| := by simp
    _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hstrip

/-- M2: the existing tent quadratic strip decay transfers uniformly to every
mollified tent. -/
theorem norm_paperFT_dictionaryTentMollified_mul_sq_le
    {L : ℝ} (hL : 0 < L) (n : ℕ) (z : ℂ)
    (hstrip : |z.im| ≤ 1 / 2) :
    ‖Zeta23.paperFT (dictionaryTentMollified L n) z‖ * ‖z‖ ^ 2
      ≤ Real.exp (1 / 2) *
        (2 * (1 + Real.exp (L / 2)) / L) := by
  rw [paperFT_dictionaryTentMollified_factor hL n z, norm_mul]
  have hphi := norm_dictionaryTentMollifierTransform_le_exp_half n hstrip
  have htent := norm_paperFT_dictionaryTent_mul_sq_le hL z hstrip
  calc
    (‖dictionaryTentMollifierTransform n z‖ *
        ‖Zeta23.paperFT (dictionaryTent L) z‖) * ‖z‖ ^ 2 =
        ‖dictionaryTentMollifierTransform n z‖ *
          (‖Zeta23.paperFT (dictionaryTent L) z‖ * ‖z‖ ^ 2) := by ring
    _ ≤ Real.exp (1 / 2) *
          (‖Zeta23.paperFT (dictionaryTent L) z‖ * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hphi (by positivity)
    _ ≤ Real.exp (1 / 2) *
          (2 * (1 + Real.exp (L / 2)) / L) :=
      mul_le_mul_of_nonneg_left htent (Real.exp_pos _).le

end Zeta23.CCM

#print axioms Zeta23.CCM.paperFT_dictionaryTentMollified_factor
#print axioms Zeta23.CCM.norm_paperFT_dictionaryTentMollified_mul_sq_le
