import Zeta23.CCM.DictionaryTentMollifierLimit
import Zeta23.CCM.DictionaryArchSourceBridge
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter
open scoped FourierTransform Topology

/-!
# Archimedean limit for the canonical tent mollifier

This is Route M milestone M6.

The literal tent transform is globally integrable and remains integrable after
multiplication by the square-root weight dictated by the already-proved
`mu - mu 0` growth estimate.  The exact mollifier-transform factorization
then gives one fixed integrable majorant for the full gamma-density integrand.

No explicit-formula identity is used here.
-/

private theorem continuous_paperFT_real_of_integrable
    {k : ℝ → ℂ} (hk : Integrable k) :
    Continuous (fun r : ℝ => Zeta23.paperFT k (r : ℂ)) := by
  have hF : Continuous (𝓕 k) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hk
  have heq :
      (fun r : ℝ => Zeta23.paperFT k (r : ℂ)) =
        fun r : ℝ => 𝓕 k (-r / (2 * Real.pi)) := by
    funext r
    exact Zeta23.paperFT_ofReal_eq_fourier k r
  rw [heq]
  exact hF.comp (by fun_prop)

private theorem exists_paperFT_dictionaryTent_inv_quad_bound
    {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      ‖Zeta23.paperFT (dictionaryTent L) (r : ℂ)‖ ≤
        C * (1 + r ^ 2)⁻¹ := by
  let A : ℝ := ∫ x : ℝ, ‖dictionaryTent L x‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hsupp : ∀ x : ℝ, dictionaryTent L x ≠ 0 → |x| ≤ L := by
    intro x hx
    have hmem := dictionaryTent_support_subset_Ioo hL hx
    exact (abs_lt.mpr hmem).le
  have hunif : ∀ r : ℝ,
      ‖Zeta23.paperFT (dictionaryTent L) (r : ℂ)‖ ≤ A := by
    intro r
    have h := Zeta23.norm_paperFT_le
      (integrable_dictionaryTent hL) hsupp (r : ℂ)
    simpa [A] using h
  let B : ℝ := 2 * (1 + Real.exp (L / 2)) / L
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hsq : ∀ r : ℝ,
      ‖Zeta23.paperFT (dictionaryTent L) (r : ℂ)‖ * r ^ 2 ≤ B := by
    intro r
    have h :=
      norm_paperFT_dictionaryTent_mul_sq_le hL (r : ℂ) (by simp)
    simpa [B, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h
  let C : ℝ := 2 * (A + B)
  have hC : 0 ≤ C := by
    dsimp [C]
    nlinarith
  refine ⟨C, hC, ?_⟩
  intro r
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hden : 0 < 1 + r ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hden]
  by_cases hr : r ^ 2 ≤ 1
  · have hu := hunif r
    dsimp [C]
    nlinarith
  · have hr' : 1 < r ^ 2 := lt_of_not_ge hr
    have hs := hsq r
    have hn : 0 ≤ ‖Zeta23.paperFT (dictionaryTent L) (r : ℂ)‖ := norm_nonneg _
    dsimp [C]
    nlinarith

/-- The literal tent transform is integrable on the real spectral axis. -/
theorem integrable_paperFT_dictionaryTent
    {L : ℝ} (hL : 0 < L) :
    Integrable (fun r : ℝ =>
      Zeta23.paperFT (dictionaryTent L) (r : ℂ)) := by
  obtain ⟨C, _hC, hbound⟩ :=
    exists_paperFT_dictionaryTent_inv_quad_bound hL
  have hmajor :
      Integrable (fun r : ℝ => C * (1 + r ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  exact hmajor.mono'
    (continuous_paperFT_real_of_integrable
      (integrable_dictionaryTent hL)).aestronglyMeasurable
    (Eventually.of_forall hbound)

private theorem sqrt_div_one_add_sq_le_two_mul_rpow_tent
    {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x / (1 + x ^ 2) ≤
      2 * (1 + x) ^ (-(3 / 2 : ℝ)) := by
  have h1 : 0 < 1 + x := by linarith
  have hs1 : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.2 h1
  have hsle : Real.sqrt x ≤ Real.sqrt (1 + x) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsq1 : (Real.sqrt (1 + x)) ^ 2 = 1 + x := by
    simpa using Real.sq_sqrt h1.le
  have hmul :
      Real.sqrt x * ((1 + x) * Real.sqrt (1 + x)) ≤
        (1 + x) ^ 2 := by
    calc
      Real.sqrt x * ((1 + x) * Real.sqrt (1 + x)) ≤
          Real.sqrt (1 + x) * ((1 + x) * Real.sqrt (1 + x)) := by
        exact mul_le_mul_of_nonneg_right hsle
          (mul_nonneg h1.le hs1.le)
      _ = (1 + x) ^ 2 := by
        calc
          Real.sqrt (1 + x) * ((1 + x) * Real.sqrt (1 + x)) =
              (1 + x) * (Real.sqrt (1 + x)) ^ 2 := by ring
          _ = (1 + x) * (1 + x) := by rw [hsq1]
          _ = (1 + x) ^ 2 := by ring
  have hpoly : (1 + x) ^ 2 ≤ 2 * (1 + x ^ 2) := by
    nlinarith [sq_nonneg (x - 1)]
  have hcross :
      Real.sqrt x * ((1 + x) * Real.sqrt (1 + x)) ≤
        2 * (1 + x ^ 2) := hmul.trans hpoly
  have hden1 : 0 < 1 + x ^ 2 := by positivity
  have hden2 : 0 < (1 + x) * Real.sqrt (1 + x) :=
    mul_pos h1 hs1
  have hfrac :
      Real.sqrt x / (1 + x ^ 2) ≤
        2 / ((1 + x) * Real.sqrt (1 + x)) := by
    rw [div_le_div_iff₀ hden1 hden2]
    exact hcross
  have hp :
      (1 + x) ^ (3 / 2 : ℝ) =
        (1 + x) * Real.sqrt (1 + x) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add h1]
    simp [Real.sqrt_eq_rpow]
  rw [Real.rpow_neg h1.le, hp]
  simpa [div_eq_mul_inv] using hfrac

/-- The literal tent transform is integrable against the square-root spectral
weight needed by the archimedean density growth estimate. -/
theorem integrable_norm_paperFT_dictionaryTent_mul_sqrt
    {L : ℝ} (hL : 0 < L) :
    Integrable (fun τ : ℝ =>
      ‖Zeta23.paperFT (dictionaryTent L) (τ : ℂ)‖ *
        Real.sqrt |τ / 2|) := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_paperFT_dictionaryTent_inv_quad_bound hL
  have hbase : Integrable
      (fun τ : ℝ => (1 + ‖τ‖) ^ (-(3 / 2 : ℝ))) := by
    apply integrable_one_add_norm
    norm_num
  have hmajorInt : Integrable
      (fun τ : ℝ => (2 * C) * (1 + ‖τ‖) ^ (-(3 / 2 : ℝ))) :=
    hbase.const_mul (2 * C)
  have hcont : Continuous (fun τ : ℝ =>
      ‖Zeta23.paperFT (dictionaryTent L) (τ : ℂ)‖ *
        Real.sqrt |τ / 2|) := by
    exact
      (continuous_paperFT_real_of_integrable
        (integrable_dictionaryTent hL)).norm.mul (by fun_prop)
  refine hmajorInt.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with τ
  have habs : |τ / 2| ≤ |τ| := by
    rw [abs_div]
    norm_num
  have hsqrt : Real.sqrt |τ / 2| ≤ Real.sqrt |τ| :=
    Real.sqrt_le_sqrt habs
  have hright0 : 0 ≤ C * (1 + τ ^ 2)⁻¹ :=
    mul_nonneg hC (inv_nonneg.2 (by positivity))
  have hfirst :
      ‖Zeta23.paperFT (dictionaryTent L) (τ : ℂ)‖ *
          Real.sqrt |τ / 2| ≤
        (C * (1 + τ ^ 2)⁻¹) * Real.sqrt |τ| := by
    exact mul_le_mul (hdecay τ) hsqrt (Real.sqrt_nonneg _) hright0
  have hkernel :=
    sqrt_div_one_add_sq_le_two_mul_rpow_tent
      (x := |τ|) (abs_nonneg τ)
  have hsecond :
      (C * (1 + τ ^ 2)⁻¹) * Real.sqrt |τ| ≤
        (2 * C) * (1 + |τ|) ^ (-(3 / 2 : ℝ)) := by
    have hsquare : |τ| ^ 2 = τ ^ 2 := sq_abs τ
    have hc := mul_le_mul_of_nonneg_left hkernel hC
    rw [hsquare] at hc
    calc
      (C * (1 + τ ^ 2)⁻¹) * Real.sqrt |τ| =
          C * (Real.sqrt |τ| / (1 + τ ^ 2)) := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ C * (2 * (1 + |τ|) ^ (-(3 / 2 : ℝ))) := hc
      _ = (2 * C) * (1 + |τ|) ^ (-(3 / 2 : ℝ)) := by ring
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
    hfirst.trans hsecond

private theorem measurable_mu_sub_mu_zero_tent :
    Measurable (fun τ : ℝ => Zeta23.mu τ - Zeta23.mu 0) := by
  have hterm : ∀ m : ℕ,
      Measurable (fun τ : ℝ => archDigammaAllTerm (τ / 2) m) := by
    intro m
    unfold archDigammaAllTerm
    fun_prop
  have hsum : Measurable (fun τ : ℝ =>
      ∑' m : ℕ, archDigammaAllTerm (τ / 2) m) :=
    Measurable.tsum hterm
  have heq :
      (fun τ : ℝ => Zeta23.mu τ - Zeta23.mu 0) =
        fun τ : ℝ => (1 / (2 * Real.pi)) *
          ∑' m : ℕ, archDigammaAllTerm (τ / 2) m := by
    funext τ
    exact mu_sub_mu_zero_eq_archDigammaAllSeries τ
  rw [heq]
  exact measurable_const.mul hsum

private theorem measurable_mu_tent : Measurable Zeta23.mu := by
  have hsub := measurable_mu_sub_mu_zero_tent
  have hsum : Measurable (fun τ : ℝ =>
      (Zeta23.mu τ - Zeta23.mu 0) + Zeta23.mu 0) :=
    hsub.add measurable_const
  convert hsum using 1
  funext τ
  ring

/-- The literal tent transform times the exact vertical gamma-density
difference is integrable. -/
theorem integrable_paperFT_dictionaryTent_mul_mu_sub_mu_zero
    {L : ℝ} (hL : 0 < L) :
    Integrable (fun τ : ℝ =>
      Zeta23.paperFT (dictionaryTent L) (τ : ℂ) *
        ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ)) := by
  let Cmu : ℝ :=
    (1 / (2 * Real.pi)) * ∑' m : ℕ, archHalfWeight m
  have hW := integrable_norm_paperFT_dictionaryTent_mul_sqrt hL
  have hmajor : Integrable (fun τ : ℝ =>
      Cmu *
        (‖Zeta23.paperFT (dictionaryTent L) (τ : ℂ)‖ *
          Real.sqrt |τ / 2|)) :=
    hW.const_mul Cmu
  have hmeasFT : Measurable (fun τ : ℝ =>
      Zeta23.paperFT (dictionaryTent L) (τ : ℂ)) :=
    (continuous_paperFT_real_of_integrable
      (integrable_dictionaryTent hL)).measurable
  have hmeasMu : Measurable (fun τ : ℝ =>
      ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp measurable_mu_sub_mu_zero_tent
  refine hmajor.mono' (hmeasFT.mul hmeasMu).aestronglyMeasurable ?_
  filter_upwards with τ
  have hmu0 := mu_sub_mu_zero_nonneg τ
  have hmule := mu_sub_mu_zero_le_sqrt τ
  have hnorm0 :
      0 ≤ ‖Zeta23.paperFT (dictionaryTent L) (τ : ℂ)‖ := norm_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hmule hnorm0
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmu0]
  dsimp [Cmu]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- The complete literal-tent archimedean integrand is absolutely integrable. -/
theorem integrable_paperFT_dictionaryTent_mul_mu
    {L : ℝ} (hL : 0 < L) :
    Integrable (fun τ : ℝ =>
      Zeta23.paperFT (dictionaryTent L) (τ : ℂ) *
        (Zeta23.mu τ : ℂ)) := by
  have hpaper := integrable_paperFT_dictionaryTent hL
  have hconst : Integrable (fun τ : ℝ =>
      Zeta23.paperFT (dictionaryTent L) (τ : ℂ) *
        (Zeta23.mu 0 : ℂ)) :=
    hpaper.mul_const _
  have hdiff := integrable_paperFT_dictionaryTent_mul_mu_sub_mu_zero hL
  refine (hconst.add hdiff).congr (Eventually.of_forall fun τ => ?_)
  push_cast
  ring

/-- M6: the archimedean literature channel of the canonical mollified tents
converges to the archimedean channel of the literal tent. -/
theorem dictionaryArchRHS_dictionaryTentMollified_tendsto
    {L : ℝ} (hL : 0 < L) :
    Tendsto
      (fun n : ℕ => dictionaryArchRHS (dictionaryTentMollified L n))
      atTop
      (𝓝 (dictionaryArchRHS (dictionaryTent L))) := by
  let F : ℕ → ℝ → ℂ := fun n τ =>
    Zeta23.paperFT (dictionaryTentMollified L n) (τ : ℂ) *
      (Zeta23.mu τ : ℂ)
  let f : ℝ → ℂ := fun τ =>
    Zeta23.paperFT (dictionaryTent L) (τ : ℂ) *
      (Zeta23.mu τ : ℂ)
  let bound : ℝ → ℝ := fun τ =>
    Real.exp (1 / 2 : ℝ) * ‖f τ‖
  have hboundInt : Integrable bound := by
    dsimp [bound, f]
    exact (integrable_paperFT_dictionaryTent_mul_mu hL).norm.const_mul
      (Real.exp (1 / 2 : ℝ))
  have hmeasMu : Measurable (fun τ : ℝ => (Zeta23.mu τ : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp measurable_mu_tent
  have hFmeas : ∀ n : ℕ, AEStronglyMeasurable (F n) := by
    intro n
    have hk : Integrable (dictionaryTentMollified L n) :=
      (contDiff_two_dictionaryTentMollified L n).continuous
        .integrable_of_hasCompactSupport
          (dictionaryTentMollified_hasCompactSupport hL n)
    have hft : Measurable (fun τ : ℝ =>
        Zeta23.paperFT (dictionaryTentMollified L n) (τ : ℂ)) :=
      (continuous_paperFT_real_of_integrable hk).measurable
    exact (hft.mul hmeasMu).aestronglyMeasurable
  have hdom : ∀ n : ℕ, ∀ᵐ τ : ℝ, ‖F n τ‖ ≤ bound τ := by
    intro n
    exact Eventually.of_forall fun τ => by
      have hstrip : |((τ : ℂ)).im| ≤ 1 / 2 := by simp
      have hphi :=
        norm_dictionaryTentMollifierTransform_le_exp_half n hstrip
      have hfactor :
          F n τ =
            dictionaryTentMollifierTransform n (τ : ℂ) * f τ := by
        dsimp [F, f]
        rw [paperFT_dictionaryTentMollified_factor hL n (τ : ℂ)]
        ring
      rw [hfactor, norm_mul]
      dsimp [bound]
      exact mul_le_mul_of_nonneg_right hphi (norm_nonneg _)
  have hlim : ∀ᵐ τ : ℝ,
      Tendsto (fun n : ℕ => F n τ) atTop (𝓝 (f τ)) := by
    exact Eventually.of_forall fun τ => by
      dsimp [F, f]
      exact
        (paperFT_dictionaryTentMollified_tendsto hL (τ : ℂ)).mul_const
          (Zeta23.mu τ : ℂ)
  have hDCT :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      bound hFmeas hboundInt hdom hlim
  rw [show (fun n : ℕ => dictionaryArchRHS (dictionaryTentMollified L n)) =
      fun n : ℕ => ∫ τ : ℝ, F n τ by
        funext n
        rw [dictionaryArchRHS_eq_integral_mu]
        rfl]
  rw [dictionaryArchRHS_eq_integral_mu]
  simpa [f] using hDCT

end Zeta23.CCM

#print axioms Zeta23.CCM.integrable_paperFT_dictionaryTent_mul_mu
#print axioms Zeta23.CCM.dictionaryArchRHS_dictionaryTentMollified_tendsto
