import Zeta23.OPICAFollowup.NativeSourceFamily
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Bounds for the prescribed normally convergent box product, uniform in the
real part of the Laplace variable. No strip-dependent constant is assumed. -/

noncomputable section
open Filter Finset MeasureTheory Set
open scoped Topology BigOperators
namespace Zeta23.OPICAFollowup
open Zeta23.CCM

def sourceVerticalDecayConstant : ℝ :=
  Real.log 8 * Real.sqrt UniversalSinc.fixedScale / 4

def sourceBoxProduct (w : ℂ) : ℂ :=
  UniversalSinc.product UniversalSinc.fixedScale (Complex.I*w)

lemma sourceVerticalDecayConstant_pos : 0 < sourceVerticalDecayConstant := by
  unfold sourceVerticalDecayConstant
  positivity [UniversalSinc.fixedScale_pos, Real.log_pos (by norm_num : (1 : ℝ) < 8)]

lemma complex_sin_norm_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h₁ : ‖Complex.exp (-z*Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  have h₂ : ‖Complex.exp (z*Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  norm_num
  simp only [neg_mul] at h₁ h₂
  apply (div_le_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
  exact (norm_sub_le _ _).trans (by linarith)

lemma complex_cos_norm_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h₁ : ‖Complex.exp (z*Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  have h₂ : ‖Complex.exp (-z*Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  rw [Complex.cos, norm_div]
  norm_num
  simp only [neg_mul] at h₁ h₂
  apply (div_le_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
  exact (norm_add_le _ _).trans (by linarith)

lemma complex_sinc_eq_cos_integral (z : ℂ) :
    UniversalSinc.sinc z = ∫ t : ℝ in (0:ℝ)..1, Complex.cos ((t:ℂ)*z) := by
  by_cases hz : z=0
  · simp [hz]
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Complex.sin ((t:ℂ)*z)/z)
      (Complex.cos ((t:ℂ)*z)) t := by
    have h := ((((hasDerivAt_id (t:ℂ)).mul_const z).csin).div_const z).comp_ofReal
    simpa only [id_eq, one_mul, mul_div_cancel_right₀ _ hz] using h
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t)
    ((by fun_prop : Continuous (fun t : ℝ => Complex.cos ((t:ℂ)*z))).intervalIntegrable 0 1)
  simpa [UniversalSinc.sinc_of_ne_zero hz] using hi.symm

lemma complex_sinc_norm_le_exp_abs_im (z : ℂ) :
    ‖UniversalSinc.sinc z‖ ≤ Real.exp |z.im| := by
  rw [complex_sinc_eq_cos_integral]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := Real.exp |z.im|)
    (f := fun t : ℝ => Complex.cos ((t:ℂ)*z)) (fun t ht => by
      have ht' : t ∈ Ioc (0:ℝ) 1 := by simpa using ht
      apply (complex_cos_norm_le_exp_abs_im _).trans
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        abs_mul, abs_of_pos ht'.1]
      exact mul_le_of_le_one_left (abs_nonneg _) ht'.2)
  simpa using h

lemma complex_sinc_norm_le_exp_abs_im_div {z : ℂ} (hz : z≠0) :
    ‖UniversalSinc.sinc z‖ ≤ Real.exp |z.im| / ‖z‖ := by
  rw [UniversalSinc.sinc_of_ne_zero hz, norm_div]
  exact div_le_div_of_nonneg_right (complex_sin_norm_le_exp_abs_im z) (norm_nonneg _)

lemma normalized_product_head_bound {f : ℕ → ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hunit : ∀ n, ‖f n‖ ≤ 1) (H : ℕ) (hhead : ∀ n < H, ‖f n‖ ≤ b)
    (M : ℕ) (hM : H ≤ M) : ‖∏ n ∈ range M, f n‖ ≤ b^H := by
  have hantitone : Antitone (fun N : ℕ => ‖∏ n ∈ range N, f n‖) := by
    apply antitone_nat_of_succ_le
    intro N
    rw [prod_range_succ, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hunit N) (norm_nonneg _)).trans_eq (mul_one _)
  have hbound : ∀ N ≤ H, ‖∏ n ∈ range N, f n‖ ≤ b^N := by
    intro N
    induction N with
    | zero => intro _; simp
    | succ N ih =>
      intro hN
      rw [prod_range_succ, norm_mul, pow_succ]
      exact mul_le_mul (ih ((Nat.le_succ N).trans hN)) (hhead N (Nat.lt_of_succ_le hN))
        (norm_nonneg _) (pow_nonneg hb _)
  exact (hantitone hM).trans (hbound H le_rfl)

def verticalNormalizedFactor (s σ τ : ℝ) (n : ℕ) : ℂ :=
  UniversalSinc.sinc ((UniversalSinc.width s n : ℂ)*
    (Complex.I*((σ:ℂ)+Complex.I*(τ:ℂ)))) /
      (Real.exp (UniversalSinc.width s n*|σ|) : ℂ)

lemma vertical_factor_im {s : ℝ} (hs : 0 ≤ s) (σ τ : ℝ) (n : ℕ) :
    |(((UniversalSinc.width s n : ℂ)*(Complex.I*((σ:ℂ)+Complex.I*(τ:ℂ)))).im)| =
      UniversalSinc.width s n*|σ| := by
  simp [Complex.mul_im, Complex.mul_re, abs_mul,
    abs_of_nonneg (UniversalSinc.width_nonneg hs n)]

lemma verticalNormalizedFactor_norm_le_one {s : ℝ} (hs : 0 ≤ s) (σ τ : ℝ) (n : ℕ) :
    ‖verticalNormalizedFactor s σ τ n‖ ≤ 1 := by
  unfold verticalNormalizedFactor
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply (div_le_one (Real.exp_pos _)).mpr
  simpa only [vertical_factor_im hs] using
    complex_sinc_norm_le_exp_abs_im
      ((UniversalSinc.width s n : ℂ)*(Complex.I*((σ:ℂ)+Complex.I*(τ:ℂ))))

lemma verticalNormalizedFactor_norm_le_eighth {s : ℝ} (hs : 0 < s) (σ τ : ℝ)
    {H n : ℕ} (hn : n < H) (hbudget : 8*(H:ℝ)*((H:ℝ)+1) ≤ s*|τ|) :
    ‖verticalNormalizedFactor s σ τ n‖ ≤ 1/8 := by
  have h₁ : (n:ℝ)+1 ≤ (H:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
  have h₂ : (n:ℝ)+2 ≤ (H:ℝ)+1 := by linarith
  have hdenpos : 0 < ((n:ℝ)+1)*((n:ℝ)+2) := by positivity
  have hden : ((n:ℝ)+1)*((n:ℝ)+2) ≤ (H:ℝ)*((H:ℝ)+1) :=
    mul_le_mul h₁ h₂ (by positivity) (Nat.cast_nonneg H)
  have hwidth : 8 ≤ UniversalSinc.width s n*|τ| := by
    rw [UniversalSinc.width, div_mul_eq_mul_div]
    apply (le_div_iff₀ hdenpos).mpr
    exact (mul_le_mul_of_nonneg_left hden (by norm_num : (0:ℝ)≤8)).trans
      (by nlinarith [hbudget])
  let z : ℂ := (UniversalSinc.width s n : ℂ)*(Complex.I*((σ:ℂ)+Complex.I*(τ:ℂ)))
  have hre : |z.re| = UniversalSinc.width s n*|τ| := by
    simp [z, Complex.mul_re, Complex.mul_im, abs_mul,
      abs_of_nonneg (UniversalSinc.width_nonneg hs.le n)]
  have hnorm : 8 ≤ ‖z‖ := hwidth.trans (hre ▸ Complex.abs_re_le_norm z)
  have hz : z≠0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hnorm)
  have hbound : ‖UniversalSinc.sinc z‖ ≤ Real.exp (UniversalSinc.width s n*|σ|)/8 := by
    have hb := complex_sinc_norm_le_exp_abs_im_div hz
    rw [vertical_factor_im hs.le σ τ n] at hb
    exact hb.trans (div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) hnorm)
  unfold verticalNormalizedFactor
  change ‖UniversalSinc.sinc z / (Real.exp (UniversalSinc.width s n*|σ|):ℂ)‖ ≤ _
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  nlinarith [hbound]

lemma vertical_normalized_partial_product (s σ τ : ℝ) (M : ℕ) :
    (∏ n ∈ range M, verticalNormalizedFactor s σ τ n) =
      (∏ n ∈ range M, UniversalSinc.sinc ((UniversalSinc.width s n:ℂ)*
        (Complex.I*((σ:ℂ)+Complex.I*(τ:ℂ))))) /
          (Real.exp ((∑ n ∈ range M, UniversalSinc.width s n)*|σ|) : ℂ) := by
  unfold verticalNormalizedFactor
  rw [Finset.prod_div_distrib]
  congr 1
  simp only [Finset.sum_mul, Real.exp_sum, Complex.ofReal_prod]

/-- A contracting head controls the complete normally convergent product, with
the real exponential budget paid by every factor including the infinite tail. -/
lemma source_box_product_head_bound {s : ℝ} (hs : 0 < s) (σ τ : ℝ) (H : ℕ)
    (hbudget : 8*(H:ℝ)*((H:ℝ)+1) ≤ s*|τ|) :
    ‖UniversalSinc.product s (Complex.I*((σ:ℂ)+Complex.I*(τ:ℂ)))‖ ≤
      Real.exp (s*|σ|)*(1/8:ℝ)^H := by
  have hsum : Tendsto (fun M : ℕ => ∑ n ∈ range M, UniversalSinc.width s n)
      atTop (𝓝 s) := (UniversalSinc.hasSum_width hs.le).tendsto_sum_nat
  have hden : Tendsto (fun M : ℕ =>
      (Real.exp ((∑ n ∈ range M, UniversalSinc.width s n)*|σ|):ℂ))
      atTop (𝓝 (Real.exp (s*|σ|):ℂ)) :=
    (Real.continuous_exp.continuousAt.tendsto.comp (hsum.mul_const |σ|)).ofReal
  have hnum := UniversalSinc.tendsto_partial_product hs.le
    (Complex.I*((σ:ℂ)+Complex.I*(τ:ℂ)))
  have hlim := (hnum.div hden (by exact_mod_cast Real.exp_ne_zero (s*|σ|))).norm
  have hfinal : ‖UniversalSinc.product s (Complex.I*((σ:ℂ)+Complex.I*(τ:ℂ))) /
      (Real.exp (s*|σ|):ℂ)‖ ≤ (1/8:ℝ)^H := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop H] with M hM
    change ‖(∏ n ∈ range M, UniversalSinc.sinc ((UniversalSinc.width s n:ℂ)*
      (Complex.I*((σ:ℂ)+Complex.I*(τ:ℂ))))) /
        (Real.exp ((∑ n ∈ range M, UniversalSinc.width s n)*|σ|):ℂ)‖ ≤ _
    rw [← vertical_normalized_partial_product]
    exact normalized_product_head_bound (by norm_num)
      (verticalNormalizedFactor_norm_le_one hs.le σ τ) H
      (fun n hn => verticalNormalizedFactor_norm_le_eighth hs σ τ hn hbudget) M hM
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hfinal
  exact (div_le_iff₀ (Real.exp_pos _)).mp hfinal |>.trans_eq (mul_comm _ _)

theorem source_product_vertical_bound (σ τ : ℝ) :
    ‖sourceBoxProduct ((σ:ℂ)+Complex.I*(τ:ℂ))‖ ≤
      8*Real.exp (UniversalSinc.fixedScale*|σ|)*
        Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|) := by
  let s := UniversalSinc.fixedScale
  have hs : 0<s := UniversalSinc.fixedScale_pos
  let H : ℕ := ⌊Real.sqrt (s*|τ|)/4⌋₊
  have hN0 : (0:ℝ)≤(H:ℝ) := Nat.cast_nonneg H
  have hroot : 0≤s*|τ| := mul_nonneg hs.le (abs_nonneg _)
  have hNle : (H:ℝ) ≤ Real.sqrt (s*|τ|)/4 := Nat.floor_le (by positivity)
  have hbudget : 8*(H:ℝ)*((H:ℝ)+1) ≤ s*|τ| := by
    by_cases hH : H=0
    · simpa [hH] using hroot
    · have hN1 : (1:ℝ)≤(H:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hH
      have hsq := mul_le_mul hNle hNle hN0 (by positivity)
      have hNprod : (H:ℝ)≤(H:ℝ)*(H:ℝ) := by nlinarith
      have hsqrt := Real.sq_sqrt hroot
      nlinarith
  have hfloor : Real.sqrt (s*|τ|)/4 < (H:ℝ)+1 := Nat.lt_floor_add_one _
  have hlog : 0<Real.log 8 := Real.log_pos (by norm_num)
  have hexponent : -(Real.log 8)*(H:ℝ) ≤
      Real.log 8-(Real.log 8)*Real.sqrt (s*|τ|)/4 := by nlinarith
  have hpow : (1/8:ℝ)^H = Real.exp (-(Real.log 8)*(H:ℝ)) := by
    rw [show (1/8:ℝ)=Real.exp (-Real.log 8) by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hcost : (1/8:ℝ)^H ≤ 8*Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|) := by
    rw [hpow]
    calc
      _ ≤ Real.exp (Real.log 8-(Real.log 8)*Real.sqrt (s*|τ|)/4) :=
        Real.exp_le_exp.mpr hexponent
      _ = _ := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num)]
        congr 2
        rw [Real.sqrt_mul hs.le]
        unfold sourceVerticalDecayConstant
        dsimp [s]
        ring
  have hb := source_box_product_head_bound hs σ τ H hbudget
  apply hb.trans
  change Real.exp (s*|σ|)*(1/8:ℝ)^H ≤ _
  calc
    _ ≤ Real.exp (s*|σ|)*(8*Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|)) :=
      mul_le_mul_of_nonneg_left hcost (Real.exp_nonneg _)
    _ = _ := by dsimp [s,sourceBoxProduct]; ring

end Zeta23.OPICAFollowup
