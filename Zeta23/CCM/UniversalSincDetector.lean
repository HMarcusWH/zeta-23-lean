import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The exact original sinc product: source-level prerequisites

The index `n : ℕ` represents the paper index `r = n + 1`.  The widths and
infinite product below are the specified source, not the earlier bump bank.
The product convergence and nonreal nonvanishing theorems do not assert the
existence of its compact smooth probability density or identify a Fourier
transform. Those analytic construction obligations remain separate.
-/

noncomputable section

open Filter Finset
open scoped Topology Asymptotics

namespace Zeta23.CCM.UniversalSinc

/-- The paper half-width `s / [r(r+1)]`, indexed from zero. -/
def width (s : ℝ) (n : ℕ) : ℝ := s / (((n : ℝ) + 1) * ((n : ℝ) + 2))

theorem width_pos {s : ℝ} (hs : 0 < s) (n : ℕ) : 0 < width s n := by
  unfold width
  positivity

theorem width_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : 0 ≤ width s n := by
  unfold width
  positivity

theorem width_eq_difference (s : ℝ) (n : ℕ) :
    width s n = s / ((n : ℝ) + 1) - s / ((n : ℝ) + 2) := by
  unfold width
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem sum_width_range (s : ℝ) (N : ℕ) :
    ∑ n ∈ range N, width s n = s - s / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, width_eq_difference]
    push_cast
    ring

theorem hasSum_width {s : ℝ} (hs : 0 ≤ s) : HasSum (width s) s := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => width_nonneg hs n) s).2
  simp_rw [sum_width_range]
  have ht : Tendsto (fun N : ℕ => s / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul s
  simpa using tendsto_const_nhds.sub ht

theorem hasSum_tail_width {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    HasSum (fun n : ℕ => width s (n + N)) (s / ((N : ℝ) + 1)) := by
  have ht := (hasSum_nat_add_iff' N).mpr (hasSum_width hs)
  simpa [sum_width_range] using ht

/-- Complex sinc with the removable singularity assigned its exact value. -/
def sinc (z : ℂ) : ℂ := dslope Complex.sin 0 z

@[simp] theorem sinc_zero : sinc 0 = 1 := by
  simp [sinc]

theorem sinc_of_ne_zero {z : ℂ} (hz : z ≠ 0) : sinc z = Complex.sin z / z := by
  simp [sinc, dslope_of_ne _ hz, slope, div_eq_mul_inv, mul_comm]

@[simp] theorem sinc_neg (z : ℂ) : sinc (-z) = sinc z := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [sinc_of_ne_zero hz, sinc_of_ne_zero (neg_ne_zero.mpr hz)]

theorem analyticAt_sinc_zero : AnalyticAt ℂ sinc 0 := by
  obtain ⟨p, hp⟩ := (Complex.analyticAt_sin (x := 0))
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

set_option backward.isDefEq.respectTransparency false in
theorem sinc_sub_one_isBigO : (fun z : ℂ => sinc z - 1) =O[𝓝 0] id := by
  simpa using analyticAt_sinc_zero.differentiableAt.isBigO_sub

/-- Every individual factor is nonzero off the real axis. -/
theorem sinc_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : sinc z ≠ 0 := by
  have hz0 : z ≠ 0 := by intro h; apply hz; simp [h]
  rw [sinc_of_ne_zero hz0]
  apply div_ne_zero _ hz0
  intro hsin
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hsin
  apply hz
  rw [hk]
  simp

/-- The original infinite sinc product, without a finite truncation. -/
def product (s : ℝ) (z : ℂ) : ℂ := ∏' n : ℕ, sinc ((width s n : ℂ) * z)

theorem summable_norm_width_mul {s : ℝ} (hs : 0 ≤ s) (z : ℂ) :
    Summable (fun n : ℕ => ‖(width s n : ℂ) * z‖) := by
  have hnorm : (fun n : ℕ => ‖(width s n : ℂ) * z‖) =
      (fun n : ℕ => width s n * ‖z‖) := by
    funext n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (width_nonneg hs n)]
  rw [hnorm]
  exact (hasSum_width hs).summable.mul_right ‖z‖

/-- The summable-deviation criterion, rather than convergence alone, controls
the infinite tail. -/
theorem summable_norm_sinc_sub_one {s : ℝ} (hs : 0 ≤ s) (z : ℂ) :
    Summable (fun n : ℕ => ‖sinc ((width s n : ℂ) * z) - 1‖) := by
  exact sinc_sub_one_isBigO.comp_summable_norm (summable_norm_width_mul hs z)

theorem multipliable_sinc {s : ℝ} (hs : 0 ≤ s) (z : ℂ) :
    Multipliable (fun n : ℕ => sinc ((width s n : ℂ) * z)) := by
  simpa using multipliable_one_add_of_summable (summable_norm_sinc_sub_one hs z)

/-- The exact infinite source product has no nonreal zeros. -/
theorem product_ne_zero_of_im_ne_zero {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z.im ≠ 0) : product s z ≠ 0 := by
  unfold product
  have hfactor : ∀ n : ℕ, sinc ((width s n : ℂ) * z) ≠ 0 := by
    intro n
    apply sinc_ne_zero_of_im_ne_zero
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_ne_zero (ne_of_gt (width_pos hs n)) hz
  simpa using tprod_one_add_ne_zero_of_summable
    (f := fun n : ℕ => sinc ((width s n : ℂ) * z) - 1)
    (by simpa using hfactor) (summable_norm_sinc_sub_one hs.le z)

@[simp] theorem product_zero (s : ℝ) : product s 0 = 1 := by
  simp [product]

@[simp] theorem product_neg (s : ℝ) (z : ℂ) : product s (-z) = product s z := by
  simp [product]

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.hasSum_width
#print axioms Zeta23.CCM.UniversalSinc.summable_norm_sinc_sub_one
#print axioms Zeta23.CCM.UniversalSinc.product_ne_zero_of_im_ne_zero
