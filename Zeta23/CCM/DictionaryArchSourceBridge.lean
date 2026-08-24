import Zeta23.CCM.DictionaryArchDensityBridge

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter
open scoped BigOperators FourierTransform Interval

theorem archDigammaAllTerm_pos_of_ne_zero
    {t : ℝ} (ht : t ≠ 0) (m : ℕ) :
    0 < archDigammaAllTerm t m := by
  rw [archDigammaAllTerm_eq_sq_div]
  apply div_pos
  · exact sq_pos_of_ne_zero ht
  · exact mul_pos (archSeriesAbscissa_pos m) (by positivity)

theorem tsum_archDigammaAllTerm_pos_of_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    0 < ∑' m : ℕ, archDigammaAllTerm t m := by
  have hzero : 0 < archDigammaAllTerm t 0 :=
    archDigammaAllTerm_pos_of_ne_zero ht 0
  have hle :
      archDigammaAllTerm t 0 ≤ ∑' m : ℕ, archDigammaAllTerm t m := by
    simpa using
      (summable_archDigammaAllTerm t).sum_le_tsum ({0} : Finset ℕ)
        (fun m _ => archDigammaAllTerm_nonneg t m)
  exact hzero.trans_le hle

theorem mu_sub_mu_zero_pos_of_ne_zero
    {τ : ℝ} (hτ : τ ≠ 0) :
    0 < Zeta23.mu τ - Zeta23.mu 0 := by
  rw [mu_sub_mu_zero_eq_archDigammaAllSeries]
  apply mul_pos
  · positivity
  · exact tsum_archDigammaAllTerm_pos_of_ne_zero
      (div_ne_zero hτ (by norm_num))

theorem integral_archDensity_mul_one_sub_cos_Ioi_eq (τ : ℝ) :
    (∫ x : ℝ in Ioi 0,
        archDensity x * (1 - Real.cos (τ * x))) =
      Real.pi * (Zeta23.mu τ - Zeta23.mu 0) := by
  have h := mu_sub_mu_zero_eq_archDensity_integral τ
  calc
    (∫ x : ℝ in Ioi 0,
        archDensity x * (1 - Real.cos (τ * x))) =
        Real.pi *
          ((1 / Real.pi) *
            ∫ x : ℝ in Ioi 0,
              archDensity x * (1 - Real.cos (τ * x))) := by
            field_simp [Real.pi_ne_zero]
    _ = Real.pi * (Zeta23.mu τ - Zeta23.mu 0) := by rw [← h]

theorem integrableOn_archDensity_mul_one_sub_cos_Ioi (τ : ℝ) :
    IntegrableOn
      (fun x : ℝ => archDensity x * (1 - Real.cos (τ * x)))
      (Ioi 0) := by
  by_cases hτ : τ = 0
  · subst τ
    simp
  · apply Integrable.of_integral_ne_zero
    rw [integral_archDensity_mul_one_sub_cos_Ioi_eq]
    exact ne_of_gt
      (mul_pos Real.pi_pos (mu_sub_mu_zero_pos_of_ne_zero hτ))

theorem archDensity_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < archDensity x := by
  unfold archDensity
  exact div_pos (Real.exp_pos _)
    (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))

/-- The density kernel used for the certified `τ/x` Fubini swap. -/
def archDensityFubiniIntegrand (k : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  Zeta23.paperFT k (p.1 : ℂ) *
    ((archDensity p.2 * (1 - Real.cos (p.1 * p.2)) : ℝ) : ℂ)

theorem aestronglyMeasurable_archDensityFubiniIntegrand
    {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) :
    AEStronglyMeasurable (archDensityFubiniIntegrand k)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hpaper : Integrable (fun τ : ℝ => Zeta23.paperFT k (τ : ℂ)) :=
    Zeta23.EF.integrable_paperFT_ofReal hFk
  have hscalar : Measurable (fun p : ℝ × ℝ =>
      ((archDensity p.2 * (1 - Real.cos (p.1 * p.2)) : ℝ) : ℂ)) := by
    unfold archDensity
    fun_prop
  exact hpaper.aestronglyMeasurable.comp_fst.mul
    hscalar.aestronglyMeasurable

theorem integrable_archDensityFubiniIntegrand_slice
    (k : ℝ → ℂ) (τ : ℝ) :
    Integrable (fun x : ℝ => archDensityFubiniIntegrand k (τ, x))
      (volume.restrict (Ioi 0)) := by
  have hs := integrableOn_archDensity_mul_one_sub_cos_Ioi τ
  have hsC : Integrable (fun x : ℝ =>
      ((archDensity x * (1 - Real.cos (τ * x)) : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) := hs.ofReal
  simpa [archDensityFubiniIntegrand] using
    hsC.const_mul (Zeta23.paperFT k (τ : ℂ))

theorem integral_norm_archDensityFubiniIntegrand_slice
    (k : ℝ → ℂ) (τ : ℝ) :
    (∫ x : ℝ in Ioi 0, ‖archDensityFubiniIntegrand k (τ, x)‖) =
      ‖Zeta23.paperFT k (τ : ℂ)‖ *
        (Real.pi * (Zeta23.mu τ - Zeta23.mu 0)) := by
  calc
    (∫ x : ℝ in Ioi 0, ‖archDensityFubiniIntegrand k (τ, x)‖) =
        ∫ x : ℝ in Ioi 0,
          ‖Zeta23.paperFT k (τ : ℂ)‖ *
            (archDensity x * (1 - Real.cos (τ * x))) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hρ : 0 ≤ archDensity x := (archDensity_pos_of_pos hx).le
      have hcos : 0 ≤ 1 - Real.cos (τ * x) := by
        linarith [Real.neg_one_le_cos (τ * x), Real.cos_le_one (τ * x)]
      change
        ‖Zeta23.paperFT k (τ : ℂ) *
            ((archDensity x * (1 - Real.cos (τ * x)) : ℝ) : ℂ)‖ =
          ‖Zeta23.paperFT k (τ : ℂ)‖ *
            (archDensity x * (1 - Real.cos (τ * x)))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hρ hcos)]
    _ = ‖Zeta23.paperFT k (τ : ℂ)‖ *
        (∫ x : ℝ in Ioi 0,
          archDensity x * (1 - Real.cos (τ * x))) := by
      rw [integral_const_mul]
    _ = ‖Zeta23.paperFT k (τ : ℂ)‖ *
        (Real.pi * (Zeta23.mu τ - Zeta23.mu 0)) := by
      rw [integral_archDensity_mul_one_sub_cos_Ioi_eq]

theorem integrable_archDensityFubiniIntegrand
    {k : ℝ → ℂ}
    (hFk : Integrable (𝓕 k))
    (hmu : Integrable (fun τ : ℝ =>
      Zeta23.paperFT k (τ : ℂ) *
        ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ))) :
    Integrable (archDensityFubiniIntegrand k)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hmeas := aestronglyMeasurable_archDensityFubiniIntegrand hFk
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with τ
    exact integrable_archDensityFubiniIntegrand_slice k τ
  · have houter0 : Integrable (fun τ : ℝ =>
        ‖Zeta23.paperFT k (τ : ℂ)‖ *
          (Zeta23.mu τ - Zeta23.mu 0)) := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mu_sub_mu_zero_nonneg _)] using hmu.norm
    have houter : Integrable (fun τ : ℝ =>
        ‖Zeta23.paperFT k (τ : ℂ)‖ *
          (Real.pi * (Zeta23.mu τ - Zeta23.mu 0))) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        houter0.const_mul Real.pi
    exact houter.congr (Filter.Eventually.of_forall fun τ =>
      (integral_norm_archDensityFubiniIntegrand_slice k τ).symm)

theorem integral_paperFT_eq_two_pi_mul
    {k : ℝ → ℂ}
    (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k)) :
    (∫ τ : ℝ, Zeta23.paperFT k (τ : ℂ)) =
      (((2 * Real.pi : ℝ) : ℂ) * k 0) := by
  have h := Zeta23.EF.paper_inversion hk hki hFk 0
  have h' :
      k 0 = (1 / (2 * Real.pi) : ℂ) *
        ∫ τ : ℝ, Zeta23.paperFT k (τ : ℂ) := by
    simpa using h
  have hcoeff :
      ((2 * Real.pi : ℝ) : ℂ) * (1 / (2 * Real.pi) : ℂ) = 1 := by
    push_cast
    field_simp [Real.pi_ne_zero]
  calc
    (∫ τ : ℝ, Zeta23.paperFT k (τ : ℂ)) =
        1 * (∫ τ : ℝ, Zeta23.paperFT k (τ : ℂ)) := by rw [one_mul]
    _ = (((2 * Real.pi : ℝ) : ℂ) * (1 / (2 * Real.pi) : ℂ)) *
        (∫ τ : ℝ, Zeta23.paperFT k (τ : ℂ)) := by rw [hcoeff]
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        ((1 / (2 * Real.pi) : ℂ) *
          ∫ τ : ℝ, Zeta23.paperFT k (τ : ℂ)) := by rw [mul_assoc]
    _ = ((2 * Real.pi : ℝ) : ℂ) * k 0 := by rw [← h']

theorem integral_paperFT_mul_cos_eq_two_pi_mul
    {k : ℝ → ℂ}
    (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k))
    (heven : ∀ x : ℝ, k (-x) = k x)
    (x : ℝ) :
    (∫ τ : ℝ,
        Zeta23.paperFT k (τ : ℂ) * (Real.cos (τ * x) : ℂ)) =
      (((2 * Real.pi : ℝ) : ℂ) * k x) := by
  have h := Zeta23.EF.k_add_k_neg hk hki hFk x
  have h' :
      k x + k (-x) = (1 / Real.pi : ℂ) *
        ∫ τ : ℝ,
          Zeta23.paperFT k (τ : ℂ) * (Real.cos (τ * x) : ℂ) := by
    simpa only [mul_comm x] using h
  have hcoeff : (Real.pi : ℂ) * (1 / Real.pi : ℂ) = 1 := by
    field_simp [Real.pi_ne_zero]
  calc
    (∫ τ : ℝ,
        Zeta23.paperFT k (τ : ℂ) * (Real.cos (τ * x) : ℂ)) =
        1 * (∫ τ : ℝ,
          Zeta23.paperFT k (τ : ℂ) * (Real.cos (τ * x) : ℂ)) := by rw [one_mul]
    _ = ((Real.pi : ℂ) * (1 / Real.pi : ℂ)) *
        (∫ τ : ℝ,
          Zeta23.paperFT k (τ : ℂ) * (Real.cos (τ * x) : ℂ)) := by rw [hcoeff]
    _ = (Real.pi : ℂ) *
        ((1 / Real.pi : ℂ) *
          ∫ τ : ℝ,
            Zeta23.paperFT k (τ : ℂ) * (Real.cos (τ * x) : ℂ)) := by
      rw [mul_assoc]
    _ = (Real.pi : ℂ) * (k x + k (-x)) := by rw [← h']
    _ = ((2 * Real.pi : ℝ) : ℂ) * k x := by
      rw [heven]
      push_cast
      ring

theorem integral_paperFT_mul_one_sub_cos_eq_two_pi_mul_sub
    {k : ℝ → ℂ}
    (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k))
    (heven : ∀ x : ℝ, k (-x) = k x)
    (x : ℝ) :
    (∫ τ : ℝ,
        Zeta23.paperFT k (τ : ℂ) *
          ((1 - Real.cos (τ * x) : ℝ) : ℂ)) =
      (((2 * Real.pi : ℝ) : ℂ) * (k 0 - k x)) := by
  have hpaper := Zeta23.EF.integrable_paperFT_ofReal hFk
  have hcos := Zeta23.EF.integrable_paperFT_mul_cos hFk x
  calc
    (∫ τ : ℝ,
        Zeta23.paperFT k (τ : ℂ) *
          ((1 - Real.cos (τ * x) : ℝ) : ℂ)) =
        ∫ τ : ℝ,
          (Zeta23.paperFT k (τ : ℂ) -
            Zeta23.paperFT k (τ : ℂ) * (Real.cos (τ * x) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with τ
      push_cast
      ring
    _ = (∫ τ : ℝ, Zeta23.paperFT k (τ : ℂ)) -
        ∫ τ : ℝ,
          Zeta23.paperFT k (τ : ℂ) * (Real.cos (τ * x) : ℂ) := by
      rw [integral_sub hpaper hcos]
    _ = (((2 * Real.pi : ℝ) : ℂ) * k 0) -
        (((2 * Real.pi : ℝ) : ℂ) * k x) := by
      rw [integral_paperFT_eq_two_pi_mul hk hki hFk,
        integral_paperFT_mul_cos_eq_two_pi_mul hk hki hFk heven x]
    _ = ((2 * Real.pi : ℝ) : ℂ) * (k 0 - k x) := by ring

theorem integral_archDensityFubiniIntegrand_over_tau
    {k : ℝ → ℂ}
    (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k))
    (heven : ∀ x : ℝ, k (-x) = k x)
    (x : ℝ) :
    (∫ τ : ℝ, archDensityFubiniIntegrand k (τ, x)) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((k 0 - k x) * (archDensity x : ℂ)) := by
  calc
    (∫ τ : ℝ, archDensityFubiniIntegrand k (τ, x)) =
        ∫ τ : ℝ,
          (Zeta23.paperFT k (τ : ℂ) *
            ((1 - Real.cos (τ * x) : ℝ) : ℂ)) *
              (archDensity x : ℂ) := by
      apply integral_congr_ae
      filter_upwards with τ
      unfold archDensityFubiniIntegrand
      push_cast
      ring
    _ = (∫ τ : ℝ,
          Zeta23.paperFT k (τ : ℂ) *
            ((1 - Real.cos (τ * x) : ℝ) : ℂ)) *
          (archDensity x : ℂ) := by
      rw [integral_mul_const]
    _ = (((2 * Real.pi : ℝ) : ℂ) * (k 0 - k x)) *
          (archDensity x : ℂ) := by
      rw [integral_paperFT_mul_one_sub_cos_eq_two_pi_mul_sub
        hk hki hFk heven x]
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        ((k 0 - k x) * (archDensity x : ℂ)) := by ring

theorem integrableOn_sub_mul_archDensity_Ioi
    {k : ℝ → ℂ}
    (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k))
    (heven : ∀ x : ℝ, k (-x) = k x)
    (hmu : Integrable (fun τ : ℝ =>
      Zeta23.paperFT k (τ : ℂ) *
        ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ))) :
    IntegrableOn (fun x : ℝ =>
      (k 0 - k x) * (archDensity x : ℂ)) (Ioi 0) := by
  have hprod := integrable_archDensityFubiniIntegrand hFk hmu
  have hinner : Integrable (fun x : ℝ =>
      ∫ τ : ℝ, archDensityFubiniIntegrand k (τ, x))
      (volume.restrict (Ioi 0)) := hprod.integral_prod_right
  have hscaled := hinner.const_mul (1 / ((2 * Real.pi : ℝ) : ℂ))
  refine hscaled.congr (Filter.Eventually.of_forall fun x => ?_)
  change
    (1 / ((2 * Real.pi : ℝ) : ℂ)) *
        (∫ τ : ℝ, archDensityFubiniIntegrand k (τ, x)) =
      (k 0 - k x) * (archDensity x : ℂ)
  rw [integral_archDensityFubiniIntegrand_over_tau hk hki hFk heven x]
  field_simp [Real.pi_ne_zero]

theorem ofReal_mu_sub_mu_zero_eq_archDensity_integral (τ : ℝ) :
    ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ) =
      (1 / Real.pi : ℂ) *
        ∫ x : ℝ in Ioi 0,
          ((archDensity x * (1 - Real.cos (τ * x)) : ℝ) : ℂ) := by
  have h := congrArg (fun r : ℝ => (r : ℂ))
    (mu_sub_mu_zero_eq_archDensity_integral τ)
  have hcast :
      (∫ x : ℝ in Ioi 0,
          ((archDensity x * (1 - Real.cos (τ * x)) : ℝ) : ℂ)) =
        ((∫ x : ℝ in Ioi 0,
          archDensity x * (1 - Real.cos (τ * x)) : ℝ) : ℂ) := by
    exact integral_ofReal
  calc
    ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ) =
        (((1 / Real.pi) *
          ∫ x : ℝ in Ioi 0,
            archDensity x * (1 - Real.cos (τ * x)) : ℝ) : ℂ) := h
    _ = (1 / Real.pi : ℂ) *
        ((∫ x : ℝ in Ioi 0,
          archDensity x * (1 - Real.cos (τ * x)) : ℝ) : ℂ) := by
      push_cast
      rfl
    _ = (1 / Real.pi : ℂ) *
        ∫ x : ℝ in Ioi 0,
          ((archDensity x * (1 - Real.cos (τ * x)) : ℝ) : ℂ) := by
      exact congrArg (fun z : ℂ => (1 / Real.pi : ℂ) * z) hcast.symm

theorem paperFT_mul_mu_sub_mu_zero_eq_density_slice
    (k : ℝ → ℂ) (τ : ℝ) :
    Zeta23.paperFT k (τ : ℂ) *
        ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ) =
      (1 / Real.pi : ℂ) *
        ∫ x : ℝ in Ioi 0, archDensityFubiniIntegrand k (τ, x) := by
  rw [ofReal_mu_sub_mu_zero_eq_archDensity_integral]
  calc
    Zeta23.paperFT k (τ : ℂ) *
        ((1 / Real.pi : ℂ) *
          ∫ x : ℝ in Ioi 0,
            ((archDensity x * (1 - Real.cos (τ * x)) : ℝ) : ℂ)) =
      (1 / Real.pi : ℂ) *
        (Zeta23.paperFT k (τ : ℂ) *
          ∫ x : ℝ in Ioi 0,
            ((archDensity x * (1 - Real.cos (τ * x)) : ℝ) : ℂ)) := by ring
    _ = (1 / Real.pi : ℂ) *
        ∫ x : ℝ in Ioi 0,
          Zeta23.paperFT k (τ : ℂ) *
            ((archDensity x * (1 - Real.cos (τ * x)) : ℝ) : ℂ) := by
      rw [integral_const_mul]
    _ = (1 / Real.pi : ℂ) *
        ∫ x : ℝ in Ioi 0, archDensityFubiniIntegrand k (τ, x) := by
      rfl

theorem integral_paperFT_mul_mu_sub_mu_zero_eq_archDensity_integral
    {k : ℝ → ℂ}
    (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k))
    (heven : ∀ x : ℝ, k (-x) = k x)
    (hmu : Integrable (fun τ : ℝ =>
      Zeta23.paperFT k (τ : ℂ) *
        ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ))) :
    (∫ τ : ℝ,
        Zeta23.paperFT k (τ : ℂ) *
          ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ)) =
      (2 : ℂ) * ∫ x : ℝ in Ioi 0,
        (k 0 - k x) * (archDensity x : ℂ) := by
  have hprod := integrable_archDensityFubiniIntegrand hFk hmu
  have hswap :
      (∫ τ : ℝ,
          ∫ x : ℝ in Ioi 0, archDensityFubiniIntegrand k (τ, x)) =
        ∫ x : ℝ in Ioi 0,
          ∫ τ : ℝ, archDensityFubiniIntegrand k (τ, x) := by
    exact integral_integral_swap hprod
  calc
    (∫ τ : ℝ,
        Zeta23.paperFT k (τ : ℂ) *
          ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ)) =
        ∫ τ : ℝ, (1 / Real.pi : ℂ) *
          ∫ x : ℝ in Ioi 0, archDensityFubiniIntegrand k (τ, x) := by
      apply integral_congr_ae
      filter_upwards with τ
      exact paperFT_mul_mu_sub_mu_zero_eq_density_slice k τ
    _ = (1 / Real.pi : ℂ) *
        ∫ τ : ℝ,
          ∫ x : ℝ in Ioi 0, archDensityFubiniIntegrand k (τ, x) := by
      rw [integral_const_mul]
    _ = (1 / Real.pi : ℂ) *
        ∫ x : ℝ in Ioi 0,
          ∫ τ : ℝ, archDensityFubiniIntegrand k (τ, x) := by
      rw [hswap]
    _ = (1 / Real.pi : ℂ) *
        ∫ x : ℝ in Ioi 0,
          ((2 * Real.pi : ℝ) : ℂ) *
            ((k 0 - k x) * (archDensity x : ℂ)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      exact integral_archDensityFubiniIntegrand_over_tau
        hk hki hFk heven x
    _ = (1 / Real.pi : ℂ) * ((2 * Real.pi : ℝ) : ℂ) *
        ∫ x : ℝ in Ioi 0,
          (k 0 - k x) * (archDensity x : ℂ) := by
      rw [integral_const_mul, mul_assoc]
    _ = (2 : ℂ) * ∫ x : ℝ in Ioi 0,
        (k 0 - k x) * (archDensity x : ℂ) := by
      congr 1
      push_cast
      field_simp [Real.pi_ne_zero]

theorem dictionaryArchRHS_eq_integral_mu (k : ℝ → ℂ) :
    dictionaryArchRHS k =
      ∫ τ : ℝ,
        Zeta23.paperFT k (τ : ℂ) * (Zeta23.mu τ : ℂ) := by
  simpa [dictionaryArchRHS] using Zeta23.EF.gamma_term k

theorem integrable_paperFT_mul_mu
    {k : ℝ → ℂ}
    (hFk : Integrable (𝓕 k))
    (hmu : Integrable (fun τ : ℝ =>
      Zeta23.paperFT k (τ : ℂ) *
        ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ))) :
    Integrable (fun τ : ℝ =>
      Zeta23.paperFT k (τ : ℂ) * (Zeta23.mu τ : ℂ)) := by
  have hconst : Integrable (fun τ : ℝ =>
      Zeta23.paperFT k (τ : ℂ) * (Zeta23.mu 0 : ℂ)) :=
    (Zeta23.EF.integrable_paperFT_ofReal hFk).mul_const _
  refine (hconst.add hmu).congr (Filter.Eventually.of_forall fun τ => ?_)
  change
    Zeta23.paperFT k (τ : ℂ) * (Zeta23.mu 0 : ℂ) +
        Zeta23.paperFT k (τ : ℂ) *
          ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ) =
      Zeta23.paperFT k (τ : ℂ) * (Zeta23.mu τ : ℂ)
  push_cast
  ring

theorem dictionaryArchRHS_eq_mu_zero_add_archDensity_integral
    {k : ℝ → ℂ}
    (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k))
    (heven : ∀ x : ℝ, k (-x) = k x)
    (hmu : Integrable (fun τ : ℝ =>
      Zeta23.paperFT k (τ : ℂ) *
        ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ))) :
    dictionaryArchRHS k =
      (((2 * Real.pi * Zeta23.mu 0 : ℝ) : ℂ) * k 0) +
        (2 : ℂ) * ∫ x : ℝ in Ioi 0,
          (k 0 - k x) * (archDensity x : ℂ) := by
  have hpaper := Zeta23.EF.integrable_paperFT_ofReal hFk
  have hconst : Integrable (fun τ : ℝ =>
      Zeta23.paperFT k (τ : ℂ) * (Zeta23.mu 0 : ℂ)) :=
    hpaper.mul_const _
  rw [dictionaryArchRHS_eq_integral_mu]
  calc
    (∫ τ : ℝ,
        Zeta23.paperFT k (τ : ℂ) * (Zeta23.mu τ : ℂ)) =
        ∫ τ : ℝ,
          (Zeta23.paperFT k (τ : ℂ) * (Zeta23.mu 0 : ℂ) +
            Zeta23.paperFT k (τ : ℂ) *
              ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with τ
      push_cast
      ring
    _ = (∫ τ : ℝ,
          Zeta23.paperFT k (τ : ℂ) * (Zeta23.mu 0 : ℂ)) +
        ∫ τ : ℝ,
          Zeta23.paperFT k (τ : ℂ) *
            ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ) := by
      rw [integral_add hconst hmu]
    _ = ((∫ τ : ℝ, Zeta23.paperFT k (τ : ℂ)) *
          (Zeta23.mu 0 : ℂ)) +
        ∫ τ : ℝ,
          Zeta23.paperFT k (τ : ℂ) *
            ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ) := by
      rw [integral_mul_const]
    _ = ((((2 * Real.pi : ℝ) : ℂ) * k 0) *
          (Zeta23.mu 0 : ℂ)) +
        (2 : ℂ) * ∫ x : ℝ in Ioi 0,
          (k 0 - k x) * (archDensity x : ℂ) := by
      rw [integral_paperFT_eq_two_pi_mul hk hki hFk,
        integral_paperFT_mul_mu_sub_mu_zero_eq_archDensity_integral
          hk hki hFk heven hmu]
    _ = (((2 * Real.pi * Zeta23.mu 0 : ℝ) : ℂ) * k 0) +
        (2 : ℂ) * ∫ x : ℝ in Ioi 0,
          (k 0 - k x) * (archDensity x : ℂ) := by
      push_cast
      ring

theorem dictionaryArchRHS_eq_neg_two_mul_archDensity_integral_of_zero
    {k : ℝ → ℂ}
    (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k))
    (heven : ∀ x : ℝ, k (-x) = k x)
    (hmu : Integrable (fun τ : ℝ =>
      Zeta23.paperFT k (τ : ℂ) *
        ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ)))
    (hzero : k 0 = 0) :
    dictionaryArchRHS k =
      (-2 : ℂ) * ∫ x : ℝ in Ioi 0,
        k x * (archDensity x : ℂ) := by
  have hneg :
      (∫ x : ℝ in Ioi 0, (-k x) * (archDensity x : ℂ)) =
        -(∫ x : ℝ in Ioi 0, k x * (archDensity x : ℂ)) := by
    calc
      (∫ x : ℝ in Ioi 0, (-k x) * (archDensity x : ℂ)) =
          ∫ x : ℝ in Ioi 0, -(k x * (archDensity x : ℂ)) := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = -(∫ x : ℝ in Ioi 0, k x * (archDensity x : ℂ)) := by
        rw [integral_neg]
  rw [dictionaryArchRHS_eq_mu_zero_add_archDensity_integral
    hk hki hFk heven hmu, hzero]
  simp only [mul_zero, zero_add, zero_sub]
  rw [hneg]
  ring

theorem integral_paperFT_mul_one_sub_cos_eq_neg_two_pi_mul_of_zero
    {k : ℝ → ℂ}
    (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k))
    (heven : ∀ x : ℝ, k (-x) = k x)
    (hzero : k 0 = 0)
    (x : ℝ) :
    (∫ τ : ℝ,
        Zeta23.paperFT k (τ : ℂ) *
          ((1 - Real.cos (τ * x) : ℝ) : ℂ)) =
      (-2 * Real.pi : ℂ) * k x := by
  rw [integral_paperFT_mul_one_sub_cos_eq_two_pi_mul_sub
    hk hki hFk heven x, hzero]
  push_cast
  ring

theorem integrable_paperFT_dictionarySourceTest_mul_mu
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Integrable (fun τ : ℝ =>
      Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ) *
        (Zeta23.mu τ : ℂ)) :=
  integrable_paperFT_mul_mu
    (integrable_fourier_dictionarySourceTest hL n)
    (integrable_paperFT_dictionarySourceTest_mul_mu_sub_mu_zero hL n)

theorem integral_dictionarySourceTest_mul_archDensity_Ioi_eq_interval
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    (∫ x : ℝ in Ioi 0,
        dictionarySourceTest n L x * (archDensity x : ℂ)) =
      ∫ x : ℝ in (0 : ℝ)..L,
        dictionarySourceTest n L x * (archDensity x : ℂ) := by
  let f : ℝ → ℂ := fun x =>
    dictionarySourceTest n L x * (archDensity x : ℂ)
  have hsupport :
      (∫ x : ℝ in Ici 0, f x) = ∫ x : ℝ in Icc 0 L, f x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ici Icc_subset_Ici_self
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hxL : L < x := by
      have hnle : ¬x ≤ L := by
        intro hxle
        exact hx.2 ⟨hx0, hxle⟩
      exact lt_of_not_ge hnle
    have habs : L < |x| := by simpa [abs_of_nonneg hx0] using hxL
    unfold f
    rw [dictionarySourceTest_eq_zero_of_lt_abs hL habs n, zero_mul]
  change (∫ x : ℝ in Ioi 0, f x) = ∫ x : ℝ in (0 : ℝ)..L, f x
  calc
    (∫ x : ℝ in Ioi 0, f x) = ∫ x : ℝ in Ici 0, f x :=
      integral_Ici_eq_integral_Ioi.symm
    _ = ∫ x : ℝ in Icc 0 L, f x := hsupport
    _ = ∫ x : ℝ in Ioc 0 L, f x := integral_Icc_eq_integral_Ioc
    _ = ∫ x : ℝ in (0 : ℝ)..L, f x :=
      (intervalIntegral.integral_of_le hL.le).symm

theorem dictionaryArchRHS_sourceTest
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    dictionaryArchRHS (dictionarySourceTest n L) =
      ((alphaL n L : ℝ) : ℂ) := by
  have hk := continuous_dictionarySourceTest n L
  have hki : Integrable (dictionarySourceTest n L) :=
    hk.integrable_of_hasCompactSupport
      (dictionarySourceTest_hasCompactSupport hL n)
  have hFk := integrable_fourier_dictionarySourceTest hL n
  have heven : ∀ x : ℝ,
      dictionarySourceTest n L (-x) = dictionarySourceTest n L x :=
    fun x => dictionarySourceTest_neg n L x
  have hmu :=
    integrable_paperFT_dictionarySourceTest_mul_mu_sub_mu_zero hL n
  calc
    dictionaryArchRHS (dictionarySourceTest n L) =
        (-2 : ℂ) * ∫ x : ℝ in Ioi 0,
          dictionarySourceTest n L x * (archDensity x : ℂ) :=
      dictionaryArchRHS_eq_neg_two_mul_archDensity_integral_of_zero
        hk hki hFk heven hmu (dictionarySourceTest_zero hL n)
    _ = (-2 : ℂ) * ∫ x : ℝ in (0 : ℝ)..L,
        dictionarySourceTest n L x * (archDensity x : ℂ) := by
      rw [integral_dictionarySourceTest_mul_archDensity_Ioi_eq_interval hL n]
    _ = dictionaryArchPhysicalRHS (dictionarySourceTest n L) L := by
      symm
      simp [dictionaryArchPhysicalRHS, dictionarySourceTest_zero hL n]
    _ = ((alphaL n L : ℝ) : ℂ) :=
      dictionaryArchPhysicalRHS_sourceTest hL n

end Zeta23.CCM
