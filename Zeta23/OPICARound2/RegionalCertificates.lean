import Zeta23.OPICARound2.CausalProbe
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Uniform positive margins for the actual one-copy source product and
bounded-box finite residual certificates. No zero premise enters the product bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Finset MeasureTheory
open scoped Topology BigOperators

namespace Zeta23.OPICARound2
open CCM.UniversalSinc

def ProbeParameterBox (delta0 delta1 L : ℝ) : Set ℂ :=
  {z | delta0 ≤ z.re ∧ z.re ≤ delta1 ∧ ‖z‖ ≤ L}

def probeBoxSmallProductLower (L : ℝ) : ℝ :=
  Real.exp (-(probeSigma^2 * L^2 / 3))

def probeBoxSplitProductLower (delta0 L : ℝ) (M : ℕ) : ℝ :=
  (delta0/L)^M * Real.exp (-(2*probeSigma^2*L^2 / (9*(M:ℝ)^3)))

def probeBoxMargin (delta0 delta1 L BQ : ℝ) : ℝ :=
  Real.sqrt (2*delta0) * Real.exp (-probeSigma*delta1) *
    ((1/2-delta1)^3 * (1/2+delta0) / (L+3/2)) * BQ

/-- Exact reciprocal-cube telescope for the unchanged box widths. -/
theorem regional_width_square_telescope (s : ℝ) (n : ℕ) :
    width s n ^ 2 + s^2 / (3*((n:ℝ)+1)^3*((n:ℝ)+2)^3) =
      s^2/(3*((n:ℝ)+1)^3)-s^2/(3*((n:ℝ)+2)^3) := by
  unfold width
  have h1 : (n:ℝ)+1 ≠ 0 := by positivity
  have h2 : (n:ℝ)+2 ≠ 0 := by positivity
  field_simp
  ring

theorem regional_width_square_le_telescope (s : ℝ) (n : ℕ) :
    width s n ^ 2 ≤ s^2/(3*((n:ℝ)+1)^3)-s^2/(3*((n:ℝ)+2)^3) := by
  have h := regional_width_square_telescope s n
  have hp : 0 ≤ s^2 / (3*((n:ℝ)+1)^3*((n:ℝ)+2)^3) := by positivity
  linarith

theorem regional_tail_square_sum_sharp (s : ℝ) (M K : ℕ) :
    ∑ n ∈ range K, width s (n+M)^2 ≤ s^2/(3*((M:ℝ)+1)^3) := by
  have ht : ∀ K : ℕ, (∑ n ∈ range K, width s (n+M)^2) ≤
      s^2/(3*((M:ℝ)+1)^3)-s^2/(3*(((K+M:ℕ):ℝ)+1)^3) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have hw := regional_width_square_le_telescope s (K+M)
      push_cast at hw ih ⊢
      have he : (K:ℝ)+1+(M:ℝ)+1 = (K:ℝ)+(M:ℝ)+2 := by ring
      rw [he]
      linarith
  have h := ht K
  have hp : 0 ≤ s^2/(3*(((K+M:ℕ):ℝ)+1)^3) := by positivity
  linarith

/-- The removable hyperbolic factor is still the native sinc factor. -/
def probeSinhc (z : ℂ) : ℂ := sinc (Complex.I*z)

theorem probeSinhc_zero : probeSinhc 0 = 1 := by simp [probeSinhc]

theorem probeSinhc_eq_div {z : ℂ} (hz : z ≠ 0) :
    probeSinhc z = Complex.sinh z / z := by
  rw [probeSinhc, sinc_of_ne_zero (mul_ne_zero Complex.I_ne_zero hz), mul_comm Complex.I z,
    Complex.sin_mul_I]
  field_simp

theorem probeSinhc_integral (z : ℂ) :
    probeSinhc z = (1/2:ℂ) * ∫ t : ℝ in (-1)..1, Complex.exp (z*(t:ℂ)) := by
  by_cases hz : z=0
  · norm_num [hz, probeSinhc]
  rw [probeSinhc_eq_div hz, integral_exp_mul_complex hz]
  simp only [Complex.ofReal_one, Complex.ofReal_neg, mul_one, mul_neg]
  unfold Complex.sinh
  ring

theorem probeSinhc_remainder_integral (z : ℂ) :
    probeSinhc z - 1 = (1/2:ℂ) *
      ∫ t : ℝ in (-1)..1, (Complex.exp (z*(t:ℂ)) - 1 - z*(t:ℂ)) := by
  have hExp : IntervalIntegrable (fun t : ℝ => Complex.exp (z*(t:ℂ))) volume (-1) 1 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hLin : IntervalIntegrable (fun t : ℝ => z*(t:ℂ)) volume (-1) 1 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_sub (hExp.sub (intervalIntegrable_const)) hLin,
    intervalIntegral.integral_sub hExp intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  have ht : (∫ t : ℝ in (-1)..1, (t:ℂ)) = 0 := by
    rw [intervalIntegral.integral_ofReal]
    norm_num [integral_id]
  rw [ht, mul_zero, sub_zero, probeSinhc_integral]
  norm_num
  ring

theorem probeSinhc_small_difference (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    ‖probeSinhc z - 1‖ ≤ ‖z‖^2/3 := by
  rw [probeSinhc_remainder_integral, norm_mul]
  norm_num [norm_div]
  have hb : ‖∫ t : ℝ in (-1)..1, (Complex.exp (z*(t:ℂ))-1-z*(t:ℂ))‖ ≤
      ∫ t : ℝ in (-1)..1, ‖z‖^2*t^2 := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · exact Filter.Eventually.of_forall fun t ht => by
        have ht1 : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
        have hn : ‖z*(t:ℂ)‖ ≤ 1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          nlinarith [norm_nonneg z, abs_nonneg t]
        calc
          _ ≤ ‖z*(t:ℂ)‖^2 := Complex.norm_exp_sub_one_sub_id_le hn
          _ = _ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hi : (∫ t : ℝ in (-1)..1, ‖z‖^2*t^2) = ‖z‖^2*(2/3) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  rw [hi] at hb
  nlinarith

theorem regional_log_one_sub_lower {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/2) :
    -2*u ≤ Real.log (1-u) := by
  have hp : 0 < 1-u := by linarith
  have hinv : (1-u)⁻¹ ≤ 1+2*u := by
    apply (inv_le_iff_one_le_mul₀ hp).2
    nlinarith
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  linarith

theorem probeSinhc_small_log_lower (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    -(2*‖z‖^2/3) ≤ Real.log ‖probeSinhc z‖ := by
  have hu0 : 0 ≤ ‖z‖^2/3 := by positivity
  have hu1 : ‖z‖^2/3 ≤ 1/2 := by nlinarith [norm_nonneg z]
  have hnorm : 1-‖z‖^2/3 ≤ ‖probeSinhc z‖ := by
    have ht := norm_sub_norm_le (1:ℂ) (probeSinhc z)
    rw [norm_one, norm_sub_rev] at ht
    linarith [probeSinhc_small_difference z hz]
  have hpos : 0 < 1-‖z‖^2/3 := by linarith
  have h := (regional_log_one_sub_lower hu0 hu1).trans (Real.log_le_log hpos hnorm)
  calc -(2*‖z‖^2/3) = -2*(‖z‖^2/3) := by ring
       _ ≤ _ := h

theorem probeSinhc_small_exp_lower (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    Real.exp (-(2*‖z‖^2/3)) ≤ ‖probeSinhc z‖ := by
  have hn : probeSinhc z ≠ 0 := by
    intro h
    have hd := probeSinhc_small_difference z hz
    simp [h] at hd
    nlinarith [norm_nonneg z]
  calc
    _ ≤ Real.exp (Real.log ‖probeSinhc z‖) := Real.exp_le_exp.mpr (probeSinhc_small_log_lower z hz)
    _ = _ := Real.exp_log (norm_pos_iff.mpr hn)

#print axioms regional_tail_square_sum_sharp
#print axioms probeSinhc_small_difference
#print axioms probeSinhc_small_exp_lower



/-- Reverse triangle inequality supplies the hyperbolic right-half-plane bound. -/
theorem regional_norm_sinh_lower_re (z : ℂ) : Real.sinh z.re ≤ ‖Complex.sinh z‖ := by
  have h := norm_sub_norm_le (Complex.exp z) (Complex.exp (-z))
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at h
  rw [Real.sinh_eq, Complex.sinh, norm_div]
  norm_num [norm_div] at *
  linarith

theorem regional_sinhc_norm_lower (z : ℂ) (hz : 0 < z.re) :
    z.re / ‖z‖ ≤ ‖probeSinhc z‖ := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [probeSinhc_eq_div hz0, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg z)
  exact (Real.self_le_sinh_iff.mpr hz.le).trans (regional_norm_sinh_lower_re z)

theorem regional_width_antitone {s : ℝ} (hs : 0 ≤ s) {m n : ℕ} (hmn : m ≤ n) :
    width s n ≤ width s m := by
  unfold width
  have hcast : (m:ℝ) ≤ n := by exact_mod_cast hmn
  apply div_le_div_of_nonneg_left hs (by positivity)
  nlinarith [show 0 ≤ (m:ℝ) by positivity, show 0 ≤ (n:ℝ) by positivity]

theorem regional_native_factor_eq (s : ℝ) (n : ℕ) (z : ℂ) :
    sinc ((width s n:ℂ)*(Complex.I*z)) = probeSinhc ((width s n:ℂ)*z) := by
  unfold probeSinhc
  congr 1
  ring

theorem regional_native_factor_prefix_lower {s delta0 L : ℝ} (hs : 0 < s)
    (hdelta : 0 < delta0) (z : ℂ) (hRe : delta0 ≤ z.re) (hL : ‖z‖ ≤ L) (n : ℕ) :
    delta0/L ≤ ‖sinc ((width s n:ℂ)*(Complex.I*z))‖ := by
  have hw : 0 < width s n := width_pos hs n
  have hz : 0 < z.re := hdelta.trans_le hRe
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr (by intro h; simp [h] at hz)
  have hLp : 0 < L := hn.trans_le hL
  rw [regional_native_factor_eq]
  have hArg : 0 < ((width s n:ℂ)*z).re := by simpa using mul_pos hw hz
  have h := regional_sinhc_norm_lower ((width s n:ℂ)*z) hArg
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw] at h
  have hcancel : width s n*z.re/(width s n*‖z‖) = z.re/‖z‖ := by field_simp
  rw [hcancel] at h
  apply le_trans _ h
  exact div_le_div₀ hz.le hRe hn hL

#print axioms regional_native_factor_prefix_lower



/-- A finite tail of the actual normally convergent product has a uniform
positive lower bound. The cubic budget is proved from the literal widths. -/
theorem regional_tail_finite_product_lower {s L : ℝ} (hs : 0 ≤ s) (hL0 : 0 ≤ L)
    (z : ℂ) (hL : ‖z‖ ≤ L) (M : ℕ) (hsmall : width s M*L ≤ 1/2) (K : ℕ) :
    Real.exp (-(2*s^2*L^2/(9*((M:ℝ)+1)^3))) ≤
      ‖∏ n ∈ range K, sinc ((width s (n+M):ℂ)*(Complex.I*z))‖ := by
  have hfactor (n : ℕ) : Real.exp (-(2*L^2/3)*width s (n+M)^2) ≤
      ‖sinc ((width s (n+M):ℂ)*(Complex.I*z))‖ := by
    have hw := width_nonneg hs (n+M)
    have hwm := regional_width_antitone hs (Nat.le_add_left M n)
    have harg : ‖(width s (n+M):ℂ)*z‖ ≤ width s (n+M)*L := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left hL hw
    have hsmallarg : ‖(width s (n+M):ℂ)*z‖ ≤ 1/2 :=
      harg.trans ((mul_le_mul_of_nonneg_right hwm hL0).trans hsmall)
    have hsq : ‖(width s (n+M):ℂ)*z‖^2 ≤ width s (n+M)^2*L^2 := by
      have hm := mul_self_le_mul_self (norm_nonneg _) harg
      nlinarith
    rw [regional_native_factor_eq]
    exact (Real.exp_le_exp.mpr (by nlinarith)).trans
      (probeSinhc_small_exp_lower _ hsmallarg)
  have hprod := Finset.prod_le_prod (fun n (_ : n ∈ range K) =>
    (Real.exp_pos (-(2*L^2/3)*width s (n+M)^2)).le) (fun n _ => hfactor n)
  rw [← Real.exp_sum, ← norm_prod] at hprod
  have hsum : (∑ n ∈ range K, -(2*L^2/3)*width s (n+M)^2) =
      -(2*L^2/3)*(∑ n ∈ range K, width s (n+M)^2) := by rw [Finset.mul_sum]
  rw [hsum] at hprod
  have htail := mul_le_mul_of_nonneg_left (regional_tail_square_sum_sharp s M K)
    (show 0 ≤ 2*L^2/3 by positivity)
  apply le_trans _ hprod
  apply Real.exp_le_exp.mpr
  have he : -(2*s^2*L^2/(9*((M:ℝ)+1)^3)) =
      -(2*L^2/3)*(s^2/(3*((M:ℝ)+1)^3)) := by field_simp <;> ring
  rw [he]
  linarith

/-- Exact finite-prefix alternative, retaining the literal prefix product. -/
theorem regional_product_prefix_lower {s L : ℝ} (hs : 0 ≤ s) (hL0 : 0 ≤ L)
    (z : ℂ) (hL : ‖z‖ ≤ L) (M : ℕ) (hsmall : width s M*L ≤ 1/2) :
    ‖∏ n ∈ range M, sinc ((width s n:ℂ)*(Complex.I*z))‖ *
      Real.exp (-(2*s^2*L^2/(9*((M:ℝ)+1)^3))) ≤ ‖product s (Complex.I*z)‖ := by
  have ht := ((tendsto_partial_product hs (Complex.I*z)).comp (tendsto_add_atTop_nat M)).norm
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds ht
  intro K
  have he : (∏ n ∈ range (K+M), sinc ((width s n:ℂ)*(Complex.I*z))) =
      (∏ n ∈ range M, sinc ((width s n:ℂ)*(Complex.I*z))) *
        ∏ n ∈ range K, sinc ((width s (n+M):ℂ)*(Complex.I*z)) := by
    simpa only [Nat.add_comm] using Finset.prod_range_add
      (fun n => sinc ((width s n:ℂ)*(Complex.I*z))) M K
  change _ ≤ ‖∏ n ∈ range (K+M), sinc ((width s n:ℂ)*(Complex.I*z))‖
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_left (regional_tail_finite_product_lower hs hL0 z hL M hsmall K)
    (norm_nonneg _)

#print axioms regional_product_prefix_lower

end Zeta23.OPICARound2
