import Zeta23.CCM.UniversalSincDetector
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Bounds for the exact original infinite sinc product

These are actual product bounds, established through its convergent
prefixes. No alternative source density or Fourier-identification premise
is introduced. The geometric head estimate gives an explicit real-axis
Gevrey decay bound for the prescribed widths.
-/

noncomputable section

open Filter Finset
open scoped Topology

namespace Zeta23.CCM.UniversalSinc

theorem sinc_ofReal (x : ℝ) : sinc (x : ℂ) = (Real.sinc x : ℂ) := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    rw [sinc_of_ne_zero hxc, Real.sinc_of_ne_zero hx,
      Complex.ofReal_div, Complex.ofReal_sin]

theorem sinc_norm_ofReal_le_one (x : ℝ) : ‖sinc (x : ℂ)‖ ≤ 1 := by
  rw [sinc_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sinc_le_one x

theorem sinc_norm_ofReal_le_inv_abs {x : ℝ} (hx : x ≠ 0) :
    ‖sinc (x : ℂ)‖ ≤ 1 / |x| := by
  rw [sinc_ofReal, Complex.norm_real, Real.norm_eq_abs, Real.sinc_of_ne_zero hx, abs_div]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one (x := x)) (abs_nonneg x)

def partialProduct (s x : ℝ) (N : ℕ) : ℂ :=
  ∏ n ∈ range N, sinc ((width s n : ℂ) * (x : ℂ))

theorem sinc_real_factor_norm_le_one (s x : ℝ) (n : ℕ) :
    ‖sinc ((width s n : ℂ) * (x : ℂ))‖ ≤ 1 := by
  rw [← Complex.ofReal_mul]
  exact sinc_norm_ofReal_le_one (width s n * x)

theorem partialProduct_norm_antitone (s x : ℝ) :
    Antitone (fun N : ℕ => ‖partialProduct s x N‖) := by
  apply antitone_nat_of_succ_le
  intro N
  unfold partialProduct
  rw [prod_range_succ, Complex.norm_mul]
  exact (mul_le_mul_of_nonneg_left (sinc_real_factor_norm_le_one s x N)
    (Complex.norm_nonneg _)).trans_eq (mul_one _)

theorem partialProduct_norm_le_one (s x : ℝ) (N : ℕ) :
    ‖partialProduct s x N‖ ≤ 1 := by
  have h := partialProduct_norm_antitone s x (Nat.zero_le N)
  simpa [partialProduct, Complex.norm_def] using h

private theorem bounds_complex_norm_instances_eq :
    Complex.instNormedAddCommGroup.toNorm = Complex.instNorm := by
  rfl

private theorem tendsto_partialProduct_norm {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    Tendsto (fun N : ℕ => ‖partialProduct s x N‖) atTop (𝓝 ‖product s (x : ℂ)‖) := by
  have ht := (tendsto_partial_product hs (x : ℂ)).norm
  exact ht

/-- The exact infinite product, rather than a selected truncation, has norm
at most one on the real axis. -/
theorem product_norm_ofReal_le_one {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    ‖product s (x : ℂ)‖ ≤ 1 := by
  exact le_of_tendsto (tendsto_partialProduct_norm hs x)
    (Filter.Eventually.of_forall (partialProduct_norm_le_one s x))

theorem sinc_real_factor_norm_le_half_of_head_budget {s : ℝ} (hs : 0 < s)
    (x : ℝ) {N n : ℕ} (hn : n < N)
    (hbudget : 2 * (N : ℝ) * ((N : ℝ) + 1) ≤ s * |x|) :
    ‖sinc ((width s n : ℂ) * (x : ℂ))‖ ≤ 1 / 2 := by
  have h1 : (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
  have h2 : (n : ℝ) + 2 ≤ (N : ℝ) + 1 := by linarith
  have hdenpos : 0 < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  have hden : ((n : ℝ) + 1) * ((n : ℝ) + 2) ≤ (N : ℝ) * ((N : ℝ) + 1) :=
    mul_le_mul h1 h2 (by positivity) (Nat.cast_nonneg N)
  have hscaled : 2 ≤ |width s n * x| := by
    rw [abs_mul, abs_of_pos (width_pos hs n), width, div_mul_eq_mul_div]
    apply (le_div_iff₀ hdenpos).mpr
    exact (mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 2)).trans
      (by nlinarith [hbudget])
  have hx : width s n * x ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by norm_num) hscaled)
  rw [← Complex.ofReal_mul]
  exact (sinc_norm_ofReal_le_inv_abs hx).trans
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hscaled)

/-- A geometrically contracting head controls the complete infinite tail. -/
theorem product_norm_ofReal_le_half_pow {s : ℝ} (hs : 0 < s) (x : ℝ) (N : ℕ)
    (hbudget : 2 * (N : ℝ) * ((N : ℝ) + 1) ≤ s * |x|) :
    ‖product s (x : ℂ)‖ ≤ (1 / 2 : ℝ) ^ N := by
  have hhead : ∀ i : ℕ, i ≤ N → ‖partialProduct s x i‖ ≤ (1 / 2 : ℝ) ^ i := by
    intro i
    induction i with
    | zero => intro _; simp [partialProduct, Complex.norm_def]
    | succ i ih =>
      intro hi
      have hiN : i < N := Nat.lt_of_succ_le hi
      have hprev := ih ((Nat.le_succ i).trans hi)
      unfold partialProduct at hprev ⊢
      rw [prod_range_succ, Complex.norm_mul, pow_succ]
      exact mul_le_mul hprev (sinc_real_factor_norm_le_half_of_head_budget hs x hiN hbudget)
        (Complex.norm_nonneg _) (by positivity)
  apply le_of_tendsto (tendsto_partialProduct_norm hs.le x)
  filter_upwards [eventually_ge_atTop N] with M hM
  exact (partialProduct_norm_antitone s x hM).trans (hhead N le_rfl)

/-- Explicit real-axis Gevrey decay for the unchanged sinc product.
The scale and constant are the original paper values. -/
theorem product_norm_ofReal_le_gevrey {s : ℝ} (hs : 0 < s) (x : ℝ) :
    ‖product s (x : ℂ)‖ ≤
      2 * Real.exp (-(Real.log 2 / 2) * Real.sqrt (s * |x|)) := by
  let N : ℕ := ⌊Real.sqrt (s * |x|) / 2⌋₊
  have hR : 0 ≤ s * |x| := mul_nonneg hs.le (abs_nonneg x)
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hNle : (N : ℝ) ≤ Real.sqrt (s * |x|) / 2 := Nat.floor_le (by positivity)
  have hbudget : 2 * (N : ℝ) * ((N : ℝ) + 1) ≤ s * |x| := by
    by_cases hN : N = 0
    · simpa [hN] using hR
    · have hNge : (1 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
      have hsq := mul_le_mul hNle hNle hNnonneg
        (show 0 ≤ Real.sqrt (s * |x|) / 2 by positivity)
      have hNprod : (N : ℝ) ≤ (N : ℝ) * (N : ℝ) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hNge hNnonneg
      have hsqrt := Real.sq_sqrt hR
      nlinarith
  have hfloor : Real.sqrt (s * |x|) / 2 < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : -(Real.log 2) * (N : ℝ) ≤
      Real.log 2 + (-(Real.log 2 / 2) * Real.sqrt (s * |x|)) := by
    have hmul := mul_le_mul_of_nonneg_left hfloor.le hlogpos.le
    nlinarith
  have hexp : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)] <;> norm_num
  have hpow : (1 / 2 : ℝ) ^ N = Real.exp (-(Real.log 2) * (N : ℝ)) := by
    calc
      _ = (Real.exp (-Real.log 2)) ^ N := by rw [hexp]
      _ = Real.exp ((N : ℝ) * (-Real.log 2)) := (Real.exp_nat_mul _ N).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ (1 / 2 : ℝ) ^ N := product_norm_ofReal_le_half_pow hs x N hbudget
    _ = Real.exp (-(Real.log 2) * (N : ℝ)) := hpow
    _ ≤ Real.exp (Real.log 2 + (-(Real.log 2 / 2) * Real.sqrt (s * |x|))) :=
      Real.exp_le_exp.mpr harg
    _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num)]

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.product_norm_ofReal_le_one
#print axioms Zeta23.CCM.UniversalSinc.product_norm_ofReal_le_half_pow
#print axioms Zeta23.CCM.UniversalSinc.product_norm_ofReal_le_gevrey
