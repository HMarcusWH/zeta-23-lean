import Zeta23.OPICAFollowup.SawtoothForce

/-!
The arithmetic spectral measure and its Stieltjes function (F2). On the log-coordinate frequency
line the mode e^(iξt) of -∂_t² + 1/4 has energy a(ξ) = ξ² + 1/4, and the actual force 𝔤 of F1 has
the spectral measure

  dω(ξ) = |ζ(1/2 + iξ)|² dξ / (2π),

a positive measure on ℝ. By (F1.4) it has the finite weighted moment ∫ dω/a = log(2π) - γ. No
finite unweighted total mass is asserted or used.

- For κ ∉ [1/4, ∞) the gap δ = dist(κ, [1/4, ∞)) > 0 gives |a/(a - κ)| ≤ 1 + |κ|/δ, so
  M(κ) = ∫ dω/(a - κ) is dominated by a multiple of 1/a uniformly on a ball around κ. It is locally
  absolutely convergent and holomorphic, with M'(κ) = ∫ dω/(a - κ)².
- For Im κ ≠ 0, Im(1/(a - κ)) = Im κ/|a - κ|², so Im M(κ)/Im κ = ∫ dω/|a - κ|² > 0 because ω ≠ 0
  (its weighted moment is positive). The weighted source bounds |M(κ)| ≤ (1 + |κ|/|Im κ|)(log(2π) - γ)
  and ∫ dω/|a - κ|² ≤ (1 + |κ|/|Im κ|)(log(2π) - γ)/|Im κ| follow from the same domination.
  Nothing here asserts that any sample is real.
-/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real NNReal ENNReal

namespace Zeta23.OPICAFollowup

section Measure

/-- The spectral energy a(ξ) = ξ² + 1/4 of the mode e^(iξt) of -∂_t² + 1/4. -/
def spectralEnergy (ξ : ℝ) : ℝ := ξ ^ 2 + 1 / 4

/-- The arithmetic spectral density |ζ(1/2 + iξ)|²/(2π). -/
def arithmeticDensity (ξ : ℝ) : ℝ := ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (2 * π)

/-- The arithmetic spectral measure dω = |ζ(1/2 + iξ)|² dξ/(2π) (positive; no finite total mass is
asserted). -/
def arithmeticSpectralMeasure : Measure ℝ :=
  volume.withDensity fun ξ => ENNReal.ofReal (arithmeticDensity ξ)

/-- The Stieltjes function M(κ) = ∫ dω(ξ)/(a(ξ) - κ). -/
def arithmeticStieltjes (κ : ℂ) : ℂ :=
  ∫ ξ, ((spectralEnergy ξ : ℂ) - κ)⁻¹ ∂arithmeticSpectralMeasure

/-- The resolvent set ℂ \ [1/4, ∞) of the spectral energy. -/
def spectralResolventSet : Set ℂ := {κ | κ.im ≠ 0 ∨ κ.re < 1 / 4}

lemma spectralResolventSet_eq : spectralResolventSet = ((↑) '' Ici (1 / 4 : ℝ) : Set ℂ)ᶜ := by
  ext κ
  change (κ.im ≠ 0 ∨ κ.re < 1 / 4) ↔ κ ∉ ((↑) '' Ici (1 / 4 : ℝ) : Set ℂ)
  simp only [mem_image, mem_Ici, not_exists, not_and]
  constructor
  · rintro (h | h) a ha rfl
    · exact h (Complex.ofReal_im a)
    · simp only [Complex.ofReal_re] at h; linarith
  · intro h
    by_contra hc
    simp only [not_or, not_lt, not_not] at hc
    exact h κ.re hc.2 (Complex.ext (by simp) (by simp [hc.1]))

lemma spectralEnergy_pos (ξ : ℝ) : 0 < spectralEnergy ξ := by
  rw [spectralEnergy]; positivity

lemma quarter_le_spectralEnergy (ξ : ℝ) : 1 / 4 ≤ spectralEnergy ξ := by
  rw [spectralEnergy]; nlinarith [sq_nonneg ξ]

lemma continuous_spectralEnergy : Continuous spectralEnergy := by
  unfold spectralEnergy; fun_prop

lemma continuous_zeta_critical_line : Continuous fun ξ : ℝ => riemannZeta (1 / 2 + ξ * I) := by
  refine continuous_iff_continuousAt.mpr fun ξ => ?_
  have hne : (1 / 2 + ξ * I : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  have hc : ContinuousAt (fun ξ : ℝ => (1 / 2 + ξ * I : ℂ)) ξ := by fun_prop
  exact ContinuousAt.comp (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt hc

lemma arithmeticDensity_nonneg (ξ : ℝ) : 0 ≤ arithmeticDensity ξ := by
  rw [arithmeticDensity]; positivity

lemma continuous_arithmeticDensity : Continuous arithmeticDensity := by
  unfold arithmeticDensity
  exact ((continuous_norm.comp continuous_zeta_critical_line).pow 2).div_const _

lemma arithmeticSpectralMeasure_eq :
    arithmeticSpectralMeasure = volume.withDensity fun ξ => ((arithmeticDensity ξ).toNNReal : ℝ≥0∞) :=
  rfl

lemma measurable_density_toNNReal : Measurable fun ξ => (arithmeticDensity ξ).toNNReal :=
  continuous_arithmeticDensity.measurable.real_toNNReal

/-- Integrals against ω are density integrals. -/
lemma integral_arithmeticSpectralMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) : ∫ ξ, g ξ ∂arithmeticSpectralMeasure = ∫ ξ, arithmeticDensity ξ • g ξ := by
  rw [arithmeticSpectralMeasure_eq, integral_withDensity_eq_integral_smul measurable_density_toNNReal]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (arithmeticDensity_nonneg ξ)]

lemma integrable_arithmeticSpectralMeasure_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} :
    Integrable g arithmeticSpectralMeasure ↔ Integrable fun ξ => arithmeticDensity ξ • g ξ := by
  rw [arithmeticSpectralMeasure_eq, integrable_withDensity_iff_integrable_smul measurable_density_toNNReal]
  refine integrable_congr (Eventually.of_forall fun ξ => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (arithmeticDensity_nonneg ξ)]

/-- (F1.4) as a weighted moment of ω: 1/a is ω-integrable and ∫ dω/a = log(2π) - γ. -/
theorem arithmetic_weighted_moment :
    Integrable (fun ξ => (spectralEnergy ξ)⁻¹) arithmeticSpectralMeasure ∧
    ∫ ξ, (spectralEnergy ξ)⁻¹ ∂arithmeticSpectralMeasure =
      Real.log (2 * π) - Real.eulerMascheroniConstant := by
  obtain ⟨hI, -, hM⟩ := sawtooth_weighted_zeta_moment
  have e : (fun ξ => arithmeticDensity ξ • (spectralEnergy ξ)⁻¹) =
      fun ξ : ℝ => (1 / (2 * π)) * (‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (ξ ^ 2 + 1 / 4)) := by
    funext ξ; simp only [arithmeticDensity, spectralEnergy, smul_eq_mul]; ring
  refine ⟨integrable_arithmeticSpectralMeasure_iff.mpr (e ▸ hI.const_mul _), ?_⟩
  rw [integral_arithmeticSpectralMeasure, e, integral_const_mul, hM]

lemma budget_pos : 0 < Real.log (2 * π) - Real.eulerMascheroniConstant := by
  have h4 : (4 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
  have he : Real.exp 1 < 4 := by have := Real.exp_one_lt_d9; linarith
  have hl : 1 < Real.log (2 * π) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]; linarith
  linarith [Real.eulerMascheroniConstant_lt_two_thirds]

lemma arithmeticSpectralMeasure_univ_pos : 0 < arithmeticSpectralMeasure univ := by
  refine pos_iff_ne_zero.mpr fun h => ?_
  have h0 : arithmeticSpectralMeasure = 0 := Measure.measure_univ_eq_zero.mp h
  have := arithmetic_weighted_moment.2
  rw [h0, integral_zero_measure] at this
  linarith [budget_pos]

end Measure

section Domination

/-- A positive gap from [1/4, ∞) bounds a/|a - κ|. -/
lemma norm_inv_sub_le {κ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ a : ℝ, 1 / 4 ≤ a → δ ≤ ‖(a : ℂ) - κ‖) (ξ : ℝ) :
    ‖((spectralEnergy ξ : ℂ) - κ)⁻¹‖ ≤ (1 + ‖κ‖ / δ) * (spectralEnergy ξ)⁻¹ := by
  set a := spectralEnergy ξ
  have ha : 0 < a := spectralEnergy_pos ξ
  have hd := hgap a (quarter_le_spectralEnergy ξ)
  have hne : (a : ℂ) - κ ≠ 0 := fun h => by rw [h, norm_zero] at hd; linarith
  have key : (a : ℂ) * ((a : ℂ) - κ)⁻¹ = 1 + κ * ((a : ℂ) - κ)⁻¹ := by field_simp; ring
  have hb : ‖(a : ℂ) * ((a : ℂ) - κ)⁻¹‖ ≤ 1 + ‖κ‖ / δ := by
    rw [key]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, norm_inv]
    gcongr
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hδ hd
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at hb
  rw [le_mul_inv_iff₀ ha, mul_comm]
  exact hb

lemma norm_inv_sub_le_gap {κ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ a : ℝ, 1 / 4 ≤ a → δ ≤ ‖(a : ℂ) - κ‖) (ξ : ℝ) :
    ‖((spectralEnergy ξ : ℂ) - κ)⁻¹‖ ≤ δ⁻¹ := by
  have hd := hgap _ (quarter_le_spectralEnergy ξ)
  rw [norm_inv]
  exact inv_anti₀ hδ hd

/-- Every point of the resolvent set has a positive gap from [1/4, ∞). -/
lemma exists_gap {κ : ℂ} (hκ : κ ∈ spectralResolventSet) :
    ∃ δ > 0, ∀ a : ℝ, 1 / 4 ≤ a → δ ≤ ‖(a : ℂ) - κ‖ := by
  rcases hκ with h | h
  · refine ⟨|κ.im|, abs_pos.mpr h, fun a _ => ?_⟩
    have := Complex.abs_im_le_norm ((a : ℂ) - κ)
    simpa using this
  · refine ⟨1 / 4 - κ.re, by linarith, fun a ha => ?_⟩
    have := Complex.abs_re_le_norm ((a : ℂ) - κ)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    linarith [le_abs_self (a - κ.re)]

lemma gap_ball {κ₀ : ℂ} {δ : ℝ} (hgap : ∀ a : ℝ, 1 / 4 ≤ a → δ ≤ ‖(a : ℂ) - κ₀‖)
    {κ : ℂ} (hκ : κ ∈ Metric.ball κ₀ (δ / 2)) : ∀ a : ℝ, 1 / 4 ≤ a → δ / 2 ≤ ‖(a : ℂ) - κ‖ := by
  intro a ha
  have h1 := hgap a ha
  have h2 : ‖κ - κ₀‖ < δ / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hκ
  have h3 : ‖(a : ℂ) - κ₀‖ ≤ ‖(a : ℂ) - κ‖ + ‖κ - κ₀‖ := by
    calc ‖(a : ℂ) - κ₀‖ = ‖((a : ℂ) - κ) + (κ - κ₀)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  linarith

lemma mem_resolvent_of_gap {κ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ a : ℝ, 1 / 4 ≤ a → δ ≤ ‖(a : ℂ) - κ‖) : κ ∈ spectralResolventSet := by
  by_contra h
  change ¬(κ.im ≠ 0 ∨ κ.re < 1 / 4) at h
  simp only [not_or, not_lt, not_not] at h
  have := hgap κ.re h.2
  have e : ((κ.re : ℝ) : ℂ) - κ = 0 := Complex.ext (by simp) (by simp [h.1])
  rw [e, norm_zero] at this
  linarith

theorem isOpen_spectralResolventSet : IsOpen spectralResolventSet := by
  refine Metric.isOpen_iff.mpr fun κ hκ => ?_
  obtain ⟨δ, hδ, hgap⟩ := exists_gap hκ
  exact ⟨δ / 2, by linarith, fun κ' hκ' => mem_resolvent_of_gap (by linarith) (gap_ball hgap hκ')⟩

lemma measurable_resolvent_kernel (κ : ℂ) :
    Measurable fun ξ => ((spectralEnergy ξ : ℂ) - κ)⁻¹ :=
  ((Complex.continuous_ofReal.comp continuous_spectralEnergy).sub continuous_const).measurable.inv

lemma integrable_resolvent_kernel {κ : ℂ} (hκ : κ ∈ spectralResolventSet) :
    Integrable (fun ξ => ((spectralEnergy ξ : ℂ) - κ)⁻¹) arithmeticSpectralMeasure := by
  obtain ⟨δ, hδ, hgap⟩ := exists_gap hκ
  refine (arithmetic_weighted_moment.1.const_mul (1 + ‖κ‖ / δ)).mono'
    (measurable_resolvent_kernel κ).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  exact norm_inv_sub_le hδ hgap ξ

end Domination

section Roots

/-- F2: for κ ∉ [1/4, ∞), M(κ) = ∫ dω/(a - κ) is locally absolutely convergent (dominated by a
fixed ω-integrable multiple of 1/a on a ball around each point) and holomorphic, with
M'(κ) = ∫ dω/(a - κ)². Here a(ξ) = ξ² + 1/4 and dω = |ζ(1/2 + iξ)|² dξ/(2π) is a positive measure
with finite weighted moment ∫ dω/a = log(2π) - γ. -/
theorem arithmetic_stieltjes_holomorphic :
    spectralResolventSet = ((↑) '' Ici (1 / 4 : ℝ) : Set ℂ)ᶜ ∧
    IsOpen spectralResolventSet ∧
    (∀ ξ, 0 ≤ arithmeticDensity ξ) ∧
    Integrable (fun ξ => (spectralEnergy ξ)⁻¹) arithmeticSpectralMeasure ∧
    ∫ ξ, (spectralEnergy ξ)⁻¹ ∂arithmeticSpectralMeasure =
      Real.log (2 * π) - Real.eulerMascheroniConstant ∧
    (∀ κ₀ ∈ spectralResolventSet, ∃ ε > 0, ∃ C : ℝ, ∀ κ ∈ Metric.ball κ₀ ε, ∀ ξ,
      ‖((spectralEnergy ξ : ℂ) - κ)⁻¹‖ ≤ C * (spectralEnergy ξ)⁻¹) ∧
    (∀ κ ∈ spectralResolventSet,
      Integrable (fun ξ => ((spectralEnergy ξ : ℂ) - κ)⁻¹) arithmeticSpectralMeasure) ∧
    (∀ κ ∈ spectralResolventSet, HasDerivAt arithmeticStieltjes
      (∫ ξ, (((spectralEnergy ξ : ℂ) - κ) ^ 2)⁻¹ ∂arithmeticSpectralMeasure) κ) ∧
    DifferentiableOn ℂ arithmeticStieltjes spectralResolventSet := by
  have hloc : ∀ κ₀ ∈ spectralResolventSet, ∃ ε > 0, ∃ C : ℝ, ∀ κ ∈ Metric.ball κ₀ ε, ∀ ξ,
      ‖((spectralEnergy ξ : ℂ) - κ)⁻¹‖ ≤ C * (spectralEnergy ξ)⁻¹ := by
    intro κ₀ hκ₀
    obtain ⟨δ, hδ, hgap⟩ := exists_gap hκ₀
    refine ⟨δ / 2, by linarith, 1 + (‖κ₀‖ + δ / 2) / (δ / 2), fun κ hκ ξ => ?_⟩
    refine (norm_inv_sub_le (by linarith) (gap_ball hgap hκ) ξ).trans ?_
    have hn : ‖κ‖ ≤ ‖κ₀‖ + δ / 2 := by
      have : ‖κ - κ₀‖ < δ / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hκ
      have := norm_le_norm_add_norm_sub' κ κ₀
      linarith [norm_sub_rev κ κ₀]
    have hinv : 0 ≤ (spectralEnergy ξ)⁻¹ := (inv_pos.mpr (spectralEnergy_pos ξ)).le
    gcongr
  have hderiv : ∀ κ ∈ spectralResolventSet, HasDerivAt arithmeticStieltjes
      (∫ ξ, (((spectralEnergy ξ : ℂ) - κ) ^ 2)⁻¹ ∂arithmeticSpectralMeasure) κ := by
    intro κ₀ hκ₀
    obtain ⟨δ, hδ, hgap⟩ := exists_gap hκ₀
    obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = 1 + (‖κ₀‖ + δ / 2) / (δ / 2) := ⟨_, rfl⟩
    have hbound : ∀ᵐ ξ ∂arithmeticSpectralMeasure, ∀ κ ∈ Metric.ball κ₀ (δ / 2),
        ‖(((spectralEnergy ξ : ℂ) - κ) ^ 2)⁻¹‖ ≤ (2 / δ * C) * (spectralEnergy ξ)⁻¹ := by
      refine Eventually.of_forall fun ξ κ hκ => ?_
      have hg := gap_ball hgap hκ
      have h1 := norm_inv_sub_le_gap (by linarith : 0 < δ / 2) hg ξ
      have hn : ‖κ‖ ≤ ‖κ₀‖ + δ / 2 := by
        have : ‖κ - κ₀‖ < δ / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hκ
        have := norm_le_norm_add_norm_sub' κ κ₀
        linarith [norm_sub_rev κ κ₀]
      have h2 : ‖((spectralEnergy ξ : ℂ) - κ)⁻¹‖ ≤ C * (spectralEnergy ξ)⁻¹ := by
        refine (norm_inv_sub_le (by linarith) hg ξ).trans
          (mul_le_mul_of_nonneg_right ?_ (inv_pos.mpr (spectralEnergy_pos ξ)).le)
        rw [hCdef]
        gcongr
      rw [← inv_pow, norm_pow, sq]
      have : (δ / 2)⁻¹ = 2 / δ := inv_div δ 2
      calc ‖((spectralEnergy ξ : ℂ) - κ)⁻¹‖ * ‖((spectralEnergy ξ : ℂ) - κ)⁻¹‖
          ≤ (δ / 2)⁻¹ * (C * (spectralEnergy ξ)⁻¹) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = (2 / δ * C) * (spectralEnergy ξ)⁻¹ := by rw [this]; ring
    have hdiff : ∀ᵐ ξ ∂arithmeticSpectralMeasure, ∀ κ ∈ Metric.ball κ₀ (δ / 2),
        HasDerivAt (fun κ => ((spectralEnergy ξ : ℂ) - κ)⁻¹)
          ((((spectralEnergy ξ : ℂ) - κ) ^ 2)⁻¹) κ := by
      refine Eventually.of_forall fun ξ κ hκ => ?_
      have hg := gap_ball hgap hκ (spectralEnergy ξ) (quarter_le_spectralEnergy ξ)
      have hne : (spectralEnergy ξ : ℂ) - κ ≠ 0 := fun h => by
        rw [h, norm_zero] at hg; linarith
      have := ((hasDerivAt_id' κ).const_sub (spectralEnergy ξ : ℂ)).inv hne
      rwa [neg_neg, one_div] at this
    have hmeas : ∀ᶠ κ in 𝓝 κ₀, AEStronglyMeasurable (fun ξ => ((spectralEnergy ξ : ℂ) - κ)⁻¹)
        arithmeticSpectralMeasure :=
      Eventually.of_forall fun κ => (measurable_resolvent_kernel κ).aestronglyMeasurable
    have hmeas' : AEStronglyMeasurable (fun ξ => (((spectralEnergy ξ : ℂ) - κ₀) ^ 2)⁻¹)
        arithmeticSpectralMeasure :=
      (((Complex.continuous_ofReal.comp continuous_spectralEnergy).sub continuous_const).pow 2).measurable.inv.aestronglyMeasurable
    have hbi : Integrable (fun ξ => (2 / δ * C) * (spectralEnergy ξ)⁻¹) arithmeticSpectralMeasure :=
      arithmetic_weighted_moment.1.const_mul _
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun κ ξ => ((spectralEnergy ξ : ℂ) - κ)⁻¹)
      (F' := fun κ ξ => (((spectralEnergy ξ : ℂ) - κ) ^ 2)⁻¹) (x₀ := κ₀)
      (bound := fun ξ => (2 / δ * C) * (spectralEnergy ξ)⁻¹)
      (Metric.ball_mem_nhds κ₀ (by linarith : (0 : ℝ) < δ / 2)) hmeas (integrable_resolvent_kernel hκ₀)
      hmeas' hbound hbi hdiff
    exact h.2
  refine ⟨spectralResolventSet_eq, isOpen_spectralResolventSet, arithmeticDensity_nonneg,
    arithmetic_weighted_moment.1, arithmetic_weighted_moment.2, hloc,
    fun κ hκ => integrable_resolvent_kernel hκ, hderiv,
    fun κ hκ => (hderiv κ hκ).differentiableAt.differentiableWithinAt⟩

/-- F2: for Im κ ≠ 0, Im M(κ)/Im κ = ∫ dω/|a - κ|² > 0, with the explicit weighted source bounds
|M(κ)| ≤ (1 + |κ|/|Im κ|)(log(2π) - γ) and ∫ dω/|a - κ|² ≤ (1 + |κ|/|Im κ|)(log(2π) - γ)/|Im κ|.
No reality of any sample is asserted. -/
theorem arithmetic_stieltjes_sign_budget {κ : ℂ} (hκ : κ.im ≠ 0) :
    Integrable (fun ξ => (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹) arithmeticSpectralMeasure ∧
    (arithmeticStieltjes κ).im / κ.im =
      ∫ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ∧
    0 < ∫ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ∧
    ‖arithmeticStieltjes κ‖ ≤
      (1 + ‖κ‖ / |κ.im|) * (Real.log (2 * π) - Real.eulerMascheroniConstant) ∧
    ∫ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ≤
      (1 + ‖κ‖ / |κ.im|) * (Real.log (2 * π) - Real.eulerMascheroniConstant) / |κ.im| := by
  have hR : κ ∈ spectralResolventSet := Or.inl hκ
  have hδ : 0 < |κ.im| := abs_pos.mpr hκ
  have hgap : ∀ a : ℝ, 1 / 4 ≤ a → |κ.im| ≤ ‖(a : ℂ) - κ‖ := fun a _ => by
    have := Complex.abs_im_le_norm ((a : ℂ) - κ); simpa using this
  set C := 1 + ‖κ‖ / |κ.im|
  have hW := arithmetic_weighted_moment
  have hne : ∀ ξ, (spectralEnergy ξ : ℂ) - κ ≠ 0 := fun ξ h => by
    have := hgap _ (quarter_le_spectralEnergy ξ); rw [h, norm_zero] at this; linarith
  -- pointwise bound for 1/|a - κ|²
  have hpt : ∀ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ≤ C / |κ.im| * (spectralEnergy ξ)⁻¹ := by
    intro ξ
    have h1 := norm_inv_sub_le_gap hδ hgap ξ
    have h2 := norm_inv_sub_le hδ hgap ξ
    rw [← inv_pow, ← norm_inv, sq]
    calc ‖((spectralEnergy ξ : ℂ) - κ)⁻¹‖ * ‖((spectralEnergy ξ : ℂ) - κ)⁻¹‖
        ≤ |κ.im|⁻¹ * (C * (spectralEnergy ξ)⁻¹) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = C / |κ.im| * (spectralEnergy ξ)⁻¹ := by ring
  have hmeasN : Measurable fun ξ => (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ :=
    (((Complex.continuous_ofReal.comp continuous_spectralEnergy).sub continuous_const).norm.pow 2).measurable.inv
  have hIN : Integrable (fun ξ => (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹) arithmeticSpectralMeasure := by
    refine (hW.1.const_mul (C / |κ.im|)).mono' hmeasN.aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt ξ
  -- imaginary part
  have him : ∀ ξ, (((spectralEnergy ξ : ℂ) - κ)⁻¹).im = κ.im * (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ := by
    intro ξ
    rw [Complex.inv_im, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub]
    ring
  have hIm : (arithmeticStieltjes κ).im =
      κ.im * ∫ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure := by
    rw [arithmeticStieltjes, ← Complex.imCLM_apply,
      ← ContinuousLinearMap.integral_comp_comm Complex.imCLM (integrable_resolvent_kernel hR),
      ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun ξ => by
      beta_reduce; rw [Complex.imCLM_apply, him ξ])
  have hpos : 0 < ∫ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure := by
    rw [integral_pos_iff_support_of_nonneg (fun ξ => by positivity) hIN]
    have hs : Function.support (fun ξ => (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹) = univ := by
      ext ξ
      simp only [Function.mem_support, mem_univ, iff_true]
      exact inv_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne ξ)))
    rw [hs]
    exact arithmeticSpectralMeasure_univ_pos
  refine ⟨hIN, ?_, hpos, ?_, ?_⟩
  · rw [hIm]; field_simp
  · rw [arithmeticStieltjes, ← hW.2, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun ξ => norm_nonneg _) (hW.1.const_mul C)
      (Eventually.of_forall fun ξ => norm_inv_sub_le hδ hgap ξ))
  · calc ∫ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure
        ≤ ∫ ξ, C / |κ.im| * (spectralEnergy ξ)⁻¹ ∂arithmeticSpectralMeasure :=
          integral_mono hIN (hW.1.const_mul _) hpt
      _ = C * (Real.log (2 * π) - Real.eulerMascheroniConstant) / |κ.im| := by
          rw [integral_const_mul, hW.2]; ring

end Roots

end Zeta23.OPICAFollowup
