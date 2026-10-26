import Zeta23.OPICARound2.CausalProbe
import Zeta23.OPICARound2.CertifiedEvaluation
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



theorem regional_product_small_lower {s L : ℝ} (hs : 0 ≤ s) (hL0 : 0 ≤ L)
    (z : ℂ) (hL : ‖z‖ ≤ L) (hsmall : s*L ≤ 1) :
    Real.exp (-(s^2*L^2/3)) ≤ ‖product s (Complex.I*z)‖ := by
  have hc : width s 0*L ≤ 1/2 := by
    norm_num [width]
    nlinarith
  have h := regional_product_prefix_lower hs hL0 z hL 0 hc
  norm_num only [Finset.range_zero, Finset.prod_empty, norm_one, one_mul, Nat.cast_zero,
    zero_add, one_pow, mul_one] at h
  apply le_trans _ h
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (s*L)]

theorem regional_product_split_lower {s delta0 L : ℝ} (hs : 0 < s)
    (hdelta : 0 < delta0) (z : ℂ) (hRe : delta0 ≤ z.re) (hL : ‖z‖ ≤ L)
    (M : ℕ) (hM : 1 ≤ M) (hcut : s*L/(((M:ℝ)+1)*((M:ℝ)+2)) ≤ 1/2) :
    (delta0/L)^M * Real.exp (-(2*s^2*L^2/(9*(M:ℝ)^3))) ≤
      ‖product s (Complex.I*z)‖ := by
  have hz : 0 < z.re := hdelta.trans_le hRe
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr (by intro h; simp [h] at hz)
  have hLp : 0 < L := hnorm.trans_le hL
  have hMp : 0 < (M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have hc : width s M*L ≤ 1/2 := by convert hcut using 1 <;> simp only [width]; ring
  have hp : (delta0/L)^M ≤ ‖∏ n ∈ range M, sinc ((width s n:ℂ)*(Complex.I*z))‖ := by
    rw [norm_prod]
    calc
      _ = ∏ _n ∈ range M, delta0/L := by simp [div_pow]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => (div_pos hdelta hLp).le)
        (fun n _ => regional_native_factor_prefix_lower hs hdelta z hRe hL n)
  have ht := regional_product_prefix_lower hs.le hLp.le z hL M hc
  have hd : 9*(M:ℝ)^3 ≤ 9*((M:ℝ)+1)^3 := by gcongr <;> linarith
  have hq := div_le_div_of_nonneg_left (show 0 ≤ 2*s^2*L^2 by positivity)
    (show 0 < 9*(M:ℝ)^3 by positivity) hd
  have he : Real.exp (-(2*s^2*L^2/(9*(M:ℝ)^3))) ≤
      Real.exp (-(2*s^2*L^2/(9*((M:ℝ)+1)^3))) := Real.exp_le_exp.mpr (neg_le_neg hq)
  exact (mul_le_mul hp he (Real.exp_pos _).le (norm_nonneg _)).trans ht

theorem regional_probeV_product_formula {z : ℂ} (hz : 0 < z.re) :
    probeLaplace probeV z = Complex.exp (-z*(probeSigma:ℂ)) *
      ((z-1/2)^3*(z+1/2)/(z+3/2)) * product probeSigma (Complex.I*z) := by
  have h1 : z+(1/2:ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  have h3 : z+(3/2:ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  have hp : ((Complex.I*z)^2+1/4)^2 = (z-1/2)^2*(z+1/2)^2 := by
    simp only [mul_pow, Complex.I_sq]
    ring
  have hr : ∀ a b c : ℂ, b ≠ 0 → c ≠ 0 →
      a/(b*c)*(a^2*b^2) = a^3*b/c := by
    intro a b c hb hc
    field_simp <;> ring
  rw [probeV_laplace hz.le, JPlus_one_copy_formula, hp]
  unfold CCM.nativeCompletionRationalMultiplier
  calc
    _ = Complex.exp (-z*(probeSigma:ℂ)) *
        (((z-1/2)/((z+1/2)*(z+3/2)))*((z-1/2)^2*(z+1/2)^2)) *
          product probeSigma (Complex.I*z) := by ring
    _ = _ := by rw [hr (z-1/2) (z+1/2) (z+3/2) h1 h3]
theorem regional_probeV_norm {z : ℂ} (hz : 0 < z.re) :
    ‖probeLaplace probeV z‖ = Real.exp (-probeSigma*z.re) *
      (‖z-1/2‖^3*‖z+1/2‖/‖z+3/2‖) * ‖product probeSigma (Complex.I*z)‖ := by
  rw [regional_probeV_product_formula hz]
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_exp, Complex.mul_re,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  congr 2
  congr 1
  ring

#print axioms regional_product_small_lower
#print axioms regional_product_split_lower
#print axioms regional_probeV_product_formula



theorem probeBoxMargin_pos {delta0 delta1 L BQ : ℝ}
    (h0 : 0 < delta0) (h01 : delta0 ≤ delta1) (h1 : delta1 < 1/2)
    (hL : delta1 ≤ L) (hBQ : 0 < BQ) : 0 < probeBoxMargin delta0 delta1 L BQ := by
  have hLp : 0 < L := (h0.trans_le h01).trans_le hL
  have hdiff : 0 < 1/2-delta1 := by linarith
  unfold probeBoxMargin
  positivity

theorem regional_box_rational_lower {delta0 delta1 L : ℝ}
    (h0 : 0 < delta0) (h01 : delta0 ≤ delta1) (h1 : delta1 < 1/2)
    (hL : delta1 ≤ L) {z : ℂ} (hz : z ∈ ProbeParameterBox delta0 delta1 L) :
    (1/2-delta1)^3*(1/2+delta0)/(L+3/2) ≤
      ‖z-1/2‖^3*‖z+1/2‖/‖z+3/2‖ := by
  rcases hz with ⟨hz0,hz1,hzL⟩
  have hzpos : 0 < z.re := h0.trans_le hz0
  have hminus : 1/2-delta1 ≤ ‖z-1/2‖ := by
    have h := Complex.re_le_norm ((1/2:ℂ)-z)
    rw [norm_sub_rev] at h
    norm_num at h
    linarith
  have hplus : 1/2+delta0 ≤ ‖z+1/2‖ := by
    have h := Complex.re_le_norm (z+(1/2:ℂ))
    norm_num at h
    linarith
  have hden : ‖z+3/2‖ ≤ L+3/2 := by
    have h := norm_add_le z (3/2:ℂ)
    norm_num at h
    linarith
  have hdenpos : 0 < ‖z+3/2‖ := by
    apply norm_pos_iff.mpr
    intro he
    have h := congrArg Complex.re he
    norm_num at h
    linarith
  apply div_le_div₀ (show 0 ≤ ‖z-1/2‖^3*‖z+1/2‖ by positivity) _ hdenpos hden
  exact mul_le_mul (pow_le_pow_left₀ (by linarith : 0 ≤ 1/2-delta1) hminus 3)
    hplus (by linarith) (by positivity)

theorem regional_box_margin_lower {delta0 delta1 L BQ : ℝ}
    (h0 : 0 < delta0) (h01 : delta0 ≤ delta1) (h1 : delta1 < 1/2)
    (hL : delta1 ≤ L) (hBQ0 : 0 ≤ BQ) {z : ℂ}
    (hz : z ∈ ProbeParameterBox delta0 delta1 L)
    (hBQ : BQ ≤ ‖product probeSigma (Complex.I*z)‖) :
    probeBoxMargin delta0 delta1 L BQ ≤ Real.sqrt (2*z.re)*‖probeLaplace probeV z‖ := by
  have hzpos : 0 < z.re := h0.trans_le hz.1
  have hs : Real.sqrt (2*delta0) ≤ Real.sqrt (2*z.re) := Real.sqrt_le_sqrt (by linarith [hz.1])
  have he : Real.exp (-probeSigma*delta1) ≤ Real.exp (-probeSigma*z.re) :=
    Real.exp_le_exp.mpr (by nlinarith [probeSigma_pos, hz.2.1])
  have hr := regional_box_rational_lower h0 h01 h1 hL hz
  have hr0 : 0 ≤ (1/2-delta1)^3*(1/2+delta0)/(L+3/2) := by
    have : 0 < L := (h0.trans_le h01).trans_le hL
    have : 0 < 1/2-delta1 := by linarith
    positivity
  have hm1 := mul_le_mul hs he (Real.exp_pos _).le (Real.sqrt_nonneg _)
  have hm2 := mul_le_mul hm1 hr hr0 (show 0 ≤ Real.sqrt (2*z.re)*Real.exp (-probeSigma*z.re) by positivity)
  have hm3 := mul_le_mul hm2 hBQ hBQ0
    (show 0 ≤ Real.sqrt (2*z.re)*Real.exp (-probeSigma*z.re)*
      (‖z-1/2‖^3*‖z+1/2‖/‖z+3/2‖) by positivity)
  rw [regional_probeV_norm hzpos]
  simpa only [probeBoxMargin, mul_assoc] using hm3

def ProbeBoxCutValid (L : ℝ) (M : ℕ) : Prop :=
  (M=0 ∧ probeSigma*L ≤ 1) ∨
    (1 ≤ M ∧ probeSigma*L/(((M:ℝ)+1)*((M:ℝ)+2)) ≤ 1/2)

def probeBoxProductLower (delta0 L : ℝ) (M : ℕ) : ℝ :=
  if M=0 then probeBoxSmallProductLower L else probeBoxSplitProductLower delta0 L M

/-- Explicit Section10 source margin, both guarded cut branches. -/
theorem native_product_box_margin {delta0 delta1 L : ℝ}
    (h0 : 0 < delta0) (h01 : delta0 ≤ delta1) (h1 : delta1 < 1/2)
    (hL : delta1 ≤ L) (M : ℕ) (hcut : ProbeBoxCutValid L M) :
    0 < probeBoxProductLower delta0 L M ∧
    0 < probeBoxMargin delta0 delta1 L (probeBoxProductLower delta0 L M) ∧
    ∀ z ∈ ProbeParameterBox delta0 delta1 L,
      probeBoxProductLower delta0 L M ≤ ‖product probeSigma (Complex.I*z)‖ ∧
      probeBoxMargin delta0 delta1 L (probeBoxProductLower delta0 L M) ≤
        Real.sqrt (2*z.re)*‖probeLaplace probeV z‖ := by
  have hLp : 0 < L := (h0.trans_le h01).trans_le hL
  have hp : 0 < probeBoxProductLower delta0 L M := by
    unfold probeBoxProductLower probeBoxSmallProductLower probeBoxSplitProductLower
    split_ifs
    · exact Real.exp_pos _
    · exact mul_pos (pow_pos (div_pos h0 hLp) _) (Real.exp_pos _)
  refine ⟨hp, probeBoxMargin_pos h0 h01 h1 hL hp, ?_⟩
  intro z hz
  have hprod : probeBoxProductLower delta0 L M ≤ ‖product probeSigma (Complex.I*z)‖ := by
    rcases hcut with ⟨rfl,hs⟩ | ⟨hM,hs⟩
    · simpa [probeBoxProductLower, probeBoxSmallProductLower] using
        regional_product_small_lower probeSigma_pos.le hLp.le z hz.2.2 hs
    · have hM0 : M ≠ 0 := by omega
      simpa only [probeBoxProductLower, if_neg hM0, probeBoxSplitProductLower] using
        regional_product_split_lower probeSigma_pos h0 z hz.1 hz.2.2 M hM hs
  exact ⟨hprod, regional_box_margin_lower h0 h01 h1 hL hp.le hz hprod⟩

theorem probeBoxMargin_zero_lower (delta1 L BQ : ℝ) : probeBoxMargin 0 delta1 L BQ = 0 := by
  simp [probeBoxMargin]

theorem probeBoxMargin_critical_upper (delta0 L BQ : ℝ) : probeBoxMargin delta0 (1/2) L BQ = 0 := by
  simp [probeBoxMargin]

theorem probeBoxSplitProductLower_zero_cut (delta0 L : ℝ) : probeBoxSplitProductLower delta0 L 0 = 1 := by
  simp [probeBoxSplitProductLower]

#print axioms native_product_box_margin



/-- At an actual zero in the bounded box, the literal finite native residual
must exceed the independently established source margin. -/
theorem regional_zero_residual_lower {delta0 delta1 L : ℝ}
    (h0 : 0 < delta0) (h01 : delta0 ≤ delta1) (h1 : delta1 < 1/2)
    (hL : delta1 ≤ L) (M : ℕ) (hcut : ProbeBoxCutValid L M)
    {N : ℕ} (x : Fin N → ℂ) {z : ℂ} (hz : z ∈ ProbeParameterBox delta0 delta1 L)
    (hzero : riemannZeta (1/2+z) = 0) :
    probeBoxMargin delta0 delta1 L (probeBoxProductLower delta0 L M) ≤ ‖probeResidual x‖ := by
  have hzpos : 0 < z.re := h0.trans_le hz.1
  have hne : z ≠ (1/2:ℂ) := by
    intro he
    have h := hz.2.1
    rw [he] at h
    norm_num at h
    linarith
  have hw : probeLaplace probeW z = 0 := by
    rw [probeW_laplace hzpos hne, show riemannZeta (z+1/2) = 0 by simpa only [add_comm] using hzero]
    simp
  have heval := probe_laplace_evaluation_bound z hzpos (probeResidual x)
  rw [probeResidual_laplace_dirichlet z hzpos x, hw, zero_mul, sub_zero] at heval
  exact ((native_product_box_margin h0 h01 h1 hL M hcut).2.2 z hz).2.trans heval

/-- A certified absolute square upper bound below the computed positive
source threshold excludes zeros throughout this bounded box. -/
theorem zero_region_of_finite_probe_certificate {delta0 delta1 L : ℝ}
    (h0 : 0 < delta0) (h01 : delta0 ≤ delta1) (h1 : delta1 < 1/2)
    (hL : delta1 ≤ L) (M : ℕ) (hcut : ProbeBoxCutValid L M)
    {N : ℕ} (x : Fin N → ℂ) (U : ℝ) (hU : ‖probeResidual x‖^2 ≤ U)
    (hthreshold : U < probeBoxMargin delta0 delta1 L (probeBoxProductLower delta0 L M)^2) :
    ∀ z ∈ ProbeParameterBox delta0 delta1 L, riemannZeta (1/2+z) ≠ 0 := by
  intro z hz hzero
  have hp := (native_product_box_margin h0 h01 h1 hL M hcut).2.1
  have hb := regional_zero_residual_lower h0 h01 h1 hL M hcut x hz hzero
  nlinarith [norm_nonneg (probeResidual x)]

/-- Direct composition with the genuine Euclidean P19 absolute error budget. -/
theorem zero_region_of_enclosed_probe_data {delta0 delta1 L : ℝ}
    (h0 : 0 < delta0) (h01 : delta0 ≤ delta1) (h1 : delta1 < 1/2)
    (hL : delta1 ≤ L) (M : ℕ) (hcut : ProbeBoxCutValid L M)
    {N : ℕ} (x : Fin N → ℂ) (qhat : ℝ) (bhat : Fin N → ℂ)
    (Ghat : Matrix (Fin N) (Fin N) ℂ) (epsilonQ epsilonB epsilonG : ℝ)
    (hQ : |probeQ0-qhat| ≤ epsilonQ)
    (hB : ‖probeCoefficientVector (probeTargetColumn N)-probeCoefficientVector bhat‖ ≤ epsilonB)
    (hG : ‖probeCertificateMatrix (probeGram N)-probeCertificateMatrix Ghat‖ ≤ epsilonG)
    (hthreshold : probeNominalEnergy qhat bhat Ghat x+epsilonQ+
        2*epsilonB*‖probeCoefficientVector x‖+epsilonG*‖probeCoefficientVector x‖^2 <
      probeBoxMargin delta0 delta1 L (probeBoxProductLower delta0 L M)^2) :
    ∀ z ∈ ProbeParameterBox delta0 delta1 L, riemannZeta (1/2+z) ≠ 0 := by
  exact zero_region_of_finite_probe_certificate h0 h01 h1 hL M hcut x _
    (finite_residual_certificate x qhat bhat Ghat epsilonQ epsilonB epsilonG hQ hB hG).2.1 hthreshold

#print axioms zero_region_of_finite_probe_certificate
#print axioms zero_region_of_enclosed_probe_data

end Zeta23.OPICARound2
