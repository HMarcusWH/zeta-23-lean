import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The actual degree-four window on unit endpoint collars

The core multiplier is `sin^8(πx/L)`. On every radius-one-half complex disk
about its unit collar, Jordan's inequality gives a sine lower bound `1/L`.
The reciprocal is therefore bounded by `L^8`, and Cauchy's derivative
estimate gives `L^8 * 2^m * m!`. The constants are derived from this literal
window; no derivative estimate or approximation hypothesis is supplied.
-/

noncomputable section

open Set Metric Complex
open scoped Topology

namespace Zeta23.CCM

private theorem sin_window_lower_left_half
    {L y : ℝ} (hL : 0 < L) (hylo : 1 / 2 ≤ y) (hyhi : y ≤ L / 2) :
    1 / L ≤ Real.sin (Real.pi * y / L) := by
  have htlo : 0 ≤ Real.pi * y / L := by positivity
  have hthi : Real.pi * y / L ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hL).mpr
    have hh := mul_le_mul_of_nonneg_left hyhi Real.pi_pos.le
    nlinarith
  calc
    1 / L ≤ 2 * y / L :=
      div_le_div_of_nonneg_right (by linarith) hL.le
    _ = (2 / Real.pi) * (Real.pi * y / L) := by
      field_simp [Real.pi_ne_zero, hL.ne'] <;> ring
    _ ≤ _ := Real.mul_le_sin htlo hthi

/-- The reflected Jordan bound retains exactly half a unit of real collar. -/
theorem originalDetectorWindow_sin_lower_half_collar
    {L y : ℝ} (hL : 2 ≤ L) (hylo : 1 / 2 ≤ y) (hyhi : y ≤ L - 1 / 2) :
    1 / L ≤ Real.sin (Real.pi * y / L) := by
  have hLpos : 0 < L := by linarith
  by_cases hhalf : y ≤ L / 2
  · exact sin_window_lower_left_half hLpos hylo hhalf
  · have hraw := sin_window_lower_left_half (y := L - y) hLpos
      (by linarith) (by linarith)
    have harg : Real.pi * (L - y) / L = Real.pi - Real.pi * y / L := by
      field_simp [hLpos.ne'] <;> ring
    rw [harg, Real.sin_pi_sub] at hraw
    exact hraw

private theorem complex_sin_re_eq (z : ℂ) :
    (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
  rw [Complex.sin_eq]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cosh,
    ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
    Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Every complex point in the prescribed half-unit disk stays uniformly
away from the sine zeros. -/
theorem originalDetectorWindow_complex_sin_lower
    {L x : ℝ} (hL : 2 ≤ L) (hxlo : 1 ≤ x) (hxhi : x ≤ L - 1)
    {z : ℂ} (hz : z ∈ closedBall (x : ℂ) (1 / 2 : ℝ)) :
    1 / L ≤ ‖Complex.sin ((Real.pi : ℂ) * z / (L : ℂ))‖ := by
  have hLpos : 0 < L := by linarith
  have hnorm : ‖z - (x : ℂ)‖ ≤ (1 / 2 : ℝ) := mem_closedBall_iff_norm.mp hz
  have hre : |z.re - x| ≤ (1 / 2 : ℝ) := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      (Complex.abs_re_le_norm (z - (x : ℂ))).trans hnorm
  have hylo : 1 / 2 ≤ z.re := by linarith [(abs_le.mp hre).1]
  have hyhi : z.re ≤ L - 1 / 2 := by linarith [(abs_le.mp hre).2]
  have hs := originalDetectorWindow_sin_lower_half_collar hL hylo hyhi
  have hsnonneg : 0 ≤ Real.sin (Real.pi * z.re / L) :=
    (by positivity : (0 : ℝ) ≤ 1 / L).trans hs
  have hphase : (((Real.pi : ℂ) * z / (L : ℂ))).re = Real.pi * z.re / L := by
    simp
  calc
    1 / L ≤ Real.sin (Real.pi * z.re / L) := hs
    _ ≤ Real.sin (Real.pi * z.re / L) *
        Real.cosh (((Real.pi : ℂ) * z / (L : ℂ))).im :=
      le_mul_of_one_le_right hsnonneg (Real.one_le_cosh _)
    _ = (Complex.sin ((Real.pi : ℂ) * z / (L : ℂ))).re := by
      rw [complex_sin_re_eq, hphase]
    _ ≤ _ := Complex.re_le_norm _

/-- The reciprocal of the literal `sin^8` core multiplier. -/
def originalDetectorWindowReciprocal (L : ℝ) (z : ℂ) : ℂ :=
  (Complex.sin ((Real.pi : ℂ) * z / (L : ℂ)) ^ 8)⁻¹

private theorem window_sine_ne_zero_at_collar
    {L x : ℝ} (hL : 2 ≤ L) (hxlo : 1 ≤ x) (hxhi : x ≤ L - 1) :
    Complex.sin ((Real.pi : ℂ) * (x : ℂ) / (L : ℂ)) ≠ 0 := by
  intro hzero
  have hb := originalDetectorWindow_complex_sin_lower hL hxlo hxhi
    (z := (x : ℂ)) (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1 / 2))
  rw [hzero, norm_zero] at hb
  have hLpos : 0 < L := by linarith
  exact (not_le_of_gt (div_pos (by norm_num) hLpos)) hb

private theorem windowReciprocal_differentiableOn (L : ℝ) :
    DifferentiableOn ℂ (originalDetectorWindowReciprocal L)
      {z | Complex.sin ((Real.pi : ℂ) * z / (L : ℂ)) ≠ 0} := by
  intro z hz
  have hpow : DifferentiableAt ℂ
      (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w / (L : ℂ)) ^ 8) z := by
    fun_prop
  exact (hpow.inv (pow_ne_zero 8 hz)).differentiableWithinAt

private theorem windowReciprocal_domain_isOpen (L : ℝ) :
    IsOpen {z : ℂ | Complex.sin ((Real.pi : ℂ) * z / (L : ℂ)) ≠ 0} := by
  apply isOpen_ne_fun _ continuous_const
  fun_prop

private theorem iteratedDeriv_comp_ofReal_on_open
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (m : ℕ) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    iteratedDeriv m (fun y : ℝ => f (y : ℂ)) x = iteratedDeriv m f (x : ℂ) := by
  induction m generalizing f x with
  | zero => simp only [iteratedDeriv_zero]
  | succ m ih =>
    have hEq : deriv (fun y : ℝ => f (y : ℂ)) =ᶠ[𝓝 x]
        (fun y : ℝ => deriv f (y : ℂ)) := by
      have hnear : ∀ᶠ y : ℝ in 𝓝 x, (y : ℂ) ∈ U :=
        Complex.continuous_ofReal.continuousAt (hU.mem_nhds hx)
      filter_upwards [hnear] with y hy
      exact ((hf y hy).differentiableAt (hU.mem_nhds hy)).hasDerivAt.comp_ofReal.deriv
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    exact (hEq.iteratedDeriv_eq m).trans (ih (hf.deriv hU) hx)

/-- Restricting the literal complex reciprocal to the real line preserves
every derivative on the collar. -/
theorem originalDetectorWindowReciprocal_real_iteratedDeriv_eq
    {L x : ℝ} (hL : 2 ≤ L) (hxlo : 1 ≤ x) (hxhi : x ≤ L - 1) (m : ℕ) :
    iteratedDeriv m (fun y : ℝ => originalDetectorWindowReciprocal L (y : ℂ)) x =
      iteratedDeriv m (originalDetectorWindowReciprocal L) (x : ℂ) :=
  iteratedDeriv_comp_ofReal_on_open (windowReciprocal_domain_isOpen L)
    (windowReciprocal_differentiableOn L) m (window_sine_ne_zero_at_collar hL hxlo hxhi)

/-- The reciprocal is smooth locally on the real collar. There is no claim
that it is smooth at the window zeros. -/
theorem originalDetectorWindowReciprocal_real_contDiffAt
    {L x : ℝ} (hL : 2 ≤ L) (hxlo : 1 ≤ x) (hxhi : x ≤ L - 1)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun y : ℝ => originalDetectorWindowReciprocal L (y : ℂ)) x := by
  have hcomplex : ContDiffAt ℂ n (originalDetectorWindowReciprocal L) (x : ℂ) :=
    ((windowReciprocal_differentiableOn L).contDiffOn
      (windowReciprocal_domain_isOpen L)).contDiffAt
      ((windowReciprocal_domain_isOpen L).mem_nhds
        (window_sine_ne_zero_at_collar hL hxlo hxhi))
  exact (hcomplex.restrict_scalars ℝ).comp x Complex.ofRealCLM.contDiff.contDiffAt

theorem originalDetectorWindowReciprocal_norm_le
    {L x : ℝ} (hL : 2 ≤ L) (hxlo : 1 ≤ x) (hxhi : x ≤ L - 1)
    {z : ℂ} (hz : z ∈ closedBall (x : ℂ) (1 / 2 : ℝ)) :
    ‖originalDetectorWindowReciprocal L z‖ ≤ L ^ 8 := by
  have hLpos : 0 < L := by linarith
  have hs := originalDetectorWindow_complex_sin_lower hL hxlo hxhi hz
  have hp : (1 / L) ^ 8 ≤ ‖Complex.sin ((Real.pi : ℂ) * z / (L : ℂ))‖ ^ 8 :=
    pow_le_pow_left₀ (by positivity) hs 8
  calc
    _ = 1 / ‖Complex.sin ((Real.pi : ℂ) * z / (L : ℂ))‖ ^ 8 := by
      simp only [originalDetectorWindowReciprocal, norm_inv, norm_pow, one_div]
    _ ≤ 1 / (1 / L) ^ 8 := one_div_le_one_div_of_le (by positivity) hp
    _ = _ := by field_simp [hLpos.ne'] <;> ring

/-- The complex reciprocal derivatives have an actual, source-defined
Cauchy estimate with fixed radius one half. -/
theorem originalDetectorWindowReciprocal_iteratedDeriv_le
    {L x : ℝ} (hL : 2 ≤ L) (hxlo : 1 ≤ x) (hxhi : x ≤ L - 1) (m : ℕ) :
    ‖iteratedDeriv m (originalDetectorWindowReciprocal L) (x : ℂ)‖ ≤
      L ^ 8 * 2 ^ m * (Nat.factorial m : ℝ) := by
  have hLpos : 0 < L := by linarith
  have hd : DifferentiableOn ℂ (originalDetectorWindowReciprocal L)
      (closedBall (x : ℂ) (1 / 2 : ℝ)) := by
    intro z hz
    have hsine : Complex.sin ((Real.pi : ℂ) * z / (L : ℂ)) ≠ 0 := by
      intro hzero
      have hb := originalDetectorWindow_complex_sin_lower hL hxlo hxhi hz
      rw [hzero, norm_zero] at hb
      exact (not_le_of_gt (div_pos (by norm_num) hLpos)) hb
    have hsmooth : DifferentiableAt ℂ
        (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w / (L : ℂ)) ^ 8) z := by
      fun_prop
    exact (hsmooth.inv (pow_ne_zero 8 hsine)).differentiableWithinAt
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := originalDetectorWindowReciprocal L) (c := (x : ℂ))
    (R := (1 / 2 : ℝ)) (C := L ^ 8) m (by norm_num)
    (hd.diffContOnCl_ball Subset.rfl)
    (fun z hz => originalDetectorWindowReciprocal_norm_le hL hxlo hxhi
      (mem_closedBall.mpr (le_of_eq (mem_sphere.mp hz))))
  calc
    _ ≤ (Nat.factorial m : ℝ) * L ^ 8 / (1 / 2 : ℝ) ^ m := hcauchy
    _ = _ := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow,
        div_eq_mul_inv, inv_inv]
      ring

/-- The same radius-one-half estimate controls the actual real reciprocal
jets used by the Fourier construction. -/
theorem originalDetectorWindowReciprocal_real_iteratedDeriv_le
    {L x : ℝ} (hL : 2 ≤ L) (hxlo : 1 ≤ x) (hxhi : x ≤ L - 1) (m : ℕ) :
    ‖iteratedDeriv m (fun y : ℝ => originalDetectorWindowReciprocal L (y : ℂ)) x‖ ≤
      L ^ 8 * 2 ^ m * (Nat.factorial m : ℝ) := by
  rw [originalDetectorWindowReciprocal_real_iteratedDeriv_eq hL hxlo hxhi m]
  exact originalDetectorWindowReciprocal_iteratedDeriv_le hL hxlo hxhi m

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorWindow_sin_lower_half_collar
#print axioms Zeta23.CCM.originalDetectorWindow_complex_sin_lower
#print axioms Zeta23.CCM.originalDetectorWindowReciprocal_norm_le
#print axioms Zeta23.CCM.originalDetectorWindowReciprocal_iteratedDeriv_le
#print axioms Zeta23.CCM.originalDetectorWindowReciprocal_real_iteratedDeriv_eq
#print axioms Zeta23.CCM.originalDetectorWindowReciprocal_real_contDiffAt
#print axioms Zeta23.CCM.originalDetectorWindowReciprocal_real_iteratedDeriv_le
