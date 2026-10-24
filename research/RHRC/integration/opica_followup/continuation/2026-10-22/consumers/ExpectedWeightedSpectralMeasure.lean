import Zeta23.OPICAFollowup.WeightedSpectralMeasure

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.arithmetic_stieltjes_holomorphic`
and `Zeta23.OPICAFollowup.arithmetic_stieltjes_sign_budget` (F2).

Definition audits pin a(ξ) = ξ² + 1/4, dω = |ζ(1/2 + iξ)|² dξ/(2π) as a density measure, the
Stieltjes function M(κ) = ∫ dω/(a - κ) and the resolvent set ℂ \ [1/4, ∞). Both roots are restated
in full. Domain consumers check:
- the weighted moment of ω is the F1 source norm ‖w‖₂² of the actual sawtooth weight;
- at the real resolvent point κ = -1, M is real and positive (no sign is imposed: it is computed);
- at κ = i the sign identity gives Im M(i) > 0 and the budget gives |M(i)| ≤ 2(log(2π) - γ);
- an actual off-line strip parameter (Re ρ ≠ 1/2, Im ρ ≠ 0) has Im κ ≠ 0, so κ = ρ(1 - ρ) lies in
  the resolvent set and both roots apply to it; a critical-line parameter has real κ ≥ 1/4, on
  the cut, where neither root is asserted. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real
open Zeta23.OPICAFollowup
namespace OPICAWeightedSpectralMeasureIndependent

/-! ### Definition audits -/

theorem audit_spectralEnergy (ξ : ℝ) : spectralEnergy ξ = ξ ^ 2 + 1 / 4 := rfl

theorem audit_arithmeticDensity (ξ : ℝ) :
    arithmeticDensity ξ = ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (2 * π) := rfl

theorem audit_arithmeticSpectralMeasure :
    arithmeticSpectralMeasure = volume.withDensity fun ξ => ENNReal.ofReal (arithmeticDensity ξ) := rfl

theorem audit_arithmeticStieltjes (κ : ℂ) :
    arithmeticStieltjes κ = ∫ ξ, ((spectralEnergy ξ : ℂ) - κ)⁻¹ ∂arithmeticSpectralMeasure := rfl

theorem audit_spectralResolventSet : spectralResolventSet = {κ : ℂ | κ.im ≠ 0 ∨ κ.re < 1 / 4} := rfl

/-! ### Restated roots -/

theorem expected_arithmetic_stieltjes_holomorphic :
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
    DifferentiableOn ℂ arithmeticStieltjes spectralResolventSet :=
  arithmetic_stieltjes_holomorphic

theorem expected_arithmetic_stieltjes_sign_budget {κ : ℂ} (hκ : κ.im ≠ 0) :
    Integrable (fun ξ => (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹) arithmeticSpectralMeasure ∧
    (arithmeticStieltjes κ).im / κ.im =
      ∫ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ∧
    0 < ∫ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ∧
    ‖arithmeticStieltjes κ‖ ≤
      (1 + ‖κ‖ / |κ.im|) * (Real.log (2 * π) - Real.eulerMascheroniConstant) ∧
    ∫ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ≤
      (1 + ‖κ‖ / |κ.im|) * (Real.log (2 * π) - Real.eulerMascheroniConstant) / |κ.im| :=
  arithmetic_stieltjes_sign_budget hκ

/-! ### Domain consumers -/

/-- The weighted moment of ω is the source norm ‖w‖₂² of the actual F1 sawtooth weight. -/
theorem expected_moment_is_source_norm :
    ∫ ξ, (spectralEnergy ξ)⁻¹ ∂arithmeticSpectralMeasure = ∫ t, ‖sawtoothWeight t‖ ^ 2 := by
  rw [arithmetic_stieltjes_holomorphic.2.2.2.2.1, sawtooth_weighted_zeta_moment.2.1]

/-- At the real resolvent point κ = -1 the Stieltjes value is real and positive. -/
theorem expected_real_point :
    (arithmeticStieltjes (-1)).im = 0 ∧ 0 < (arithmeticStieltjes (-1)).re := by
  have hR : (-1 : ℂ) ∈ spectralResolventSet := Or.inr (by norm_num)
  have hI := arithmetic_stieltjes_holomorphic.2.2.2.2.2.2.1 (-1) hR
  have hpt : ∀ ξ, ((spectralEnergy ξ : ℂ) - (-1))⁻¹ = (((spectralEnergy ξ + 1)⁻¹ : ℝ) : ℂ) := by
    intro ξ; push_cast; ring
  have hIr : Integrable (fun ξ => (spectralEnergy ξ + 1)⁻¹) arithmeticSpectralMeasure := by
    have := hI.norm
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp only [hpt, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (inv_pos.mpr (by linarith [spectralEnergy_pos ξ]))
  have hM : arithmeticStieltjes (-1) =
      ((∫ ξ, (spectralEnergy ξ + 1)⁻¹ ∂arithmeticSpectralMeasure : ℝ) : ℂ) := by
    rw [arithmeticStieltjes, ← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun ξ => hpt ξ)
  have hpos : 0 < ∫ ξ, (spectralEnergy ξ + 1)⁻¹ ∂arithmeticSpectralMeasure := by
    rw [integral_pos_iff_support_of_nonneg (fun ξ => (inv_pos.mpr
      (by linarith [spectralEnergy_pos ξ])).le) hIr]
    have hs : Function.support (fun ξ => (spectralEnergy ξ + 1)⁻¹) = univ := by
      ext ξ
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (inv_pos.mpr (by linarith [spectralEnergy_pos ξ])).ne'
    rw [hs]
    exact arithmeticSpectralMeasure_univ_pos
  rw [hM]
  exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact hpos⟩

/-- At κ = i: Im M(i) > 0 and |M(i)| ≤ 2(log(2π) - γ). -/
theorem expected_point_i :
    0 < (arithmeticStieltjes I).im ∧
    ‖arithmeticStieltjes I‖ ≤ 2 * (Real.log (2 * π) - Real.eulerMascheroniConstant) := by
  obtain ⟨-, h1, h2, h3, -⟩ := arithmetic_stieltjes_sign_budget (κ := I) (by simp)
  simp only [Complex.I_im, div_one, Complex.norm_I, abs_one] at h1 h3
  refine ⟨h1 ▸ h2, ?_⟩
  linarith

/-- An off-line strip parameter has Im κ ≠ 0, so κ = ρ(1 - ρ) is in the resolvent set and both
roots apply; Im κ = (1 - 2 Re ρ) Im ρ. -/
theorem expected_offline_parameter {ρ : ℂ} (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    ((ρ * (1 - ρ))).im = (1 - 2 * ρ.re) * ρ.im ∧ ((ρ * (1 - ρ))).im ≠ 0 ∧
    (ρ * (1 - ρ)) ∈ spectralResolventSet ∧
    DifferentiableAt ℂ arithmeticStieltjes ((ρ * (1 - ρ))) ∧
    0 < (arithmeticStieltjes ((ρ * (1 - ρ)))).im / ((ρ * (1 - ρ))).im := by
  have hk : ((ρ * (1 - ρ))).im = (1 - 2 * ρ.re) * ρ.im := by
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im]
    ring
  have hne : ((ρ * (1 - ρ))).im ≠ 0 := by
    rw [hk]
    exact mul_ne_zero (fun h => hre (by linarith)) him
  have hR : (ρ * (1 - ρ)) ∈ spectralResolventSet := Or.inl hne
  obtain ⟨-, h1, h2, -⟩ := arithmetic_stieltjes_sign_budget hne
  exact ⟨hk, hne, hR, (arithmetic_stieltjes_holomorphic.2.2.2.2.2.2.2.1 _ hR).differentiableAt,
    h1 ▸ h2⟩

/-- A critical-line parameter has real κ = 1/4 + (Im ρ)² on the cut [1/4, ∞): it is outside the
resolvent set, where neither root is asserted. -/
theorem expected_critical_line_on_cut {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    (ρ * (1 - ρ)) = ((1 / 4 + ρ.im ^ 2 : ℝ) : ℂ) ∧ (ρ * (1 - ρ)) ∉ spectralResolventSet := by
  have hρ : ρ = (1 / 2 : ℂ) + (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hk : (ρ * (1 - ρ)) = ((1 / 4 + ρ.im ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [hρ]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  refine ⟨hk, ?_⟩
  rw [spectralResolventSet_eq, hk, Set.notMem_compl_iff]
  exact ⟨_, by simp only [mem_Ici]; nlinarith [sq_nonneg ρ.im], rfl⟩

end OPICAWeightedSpectralMeasureIndependent

#print axioms Zeta23.OPICAFollowup.arithmetic_stieltjes_holomorphic
#print axioms Zeta23.OPICAFollowup.arithmetic_stieltjes_sign_budget
#print axioms OPICAWeightedSpectralMeasureIndependent.audit_arithmeticStieltjes
#print axioms OPICAWeightedSpectralMeasureIndependent.expected_arithmetic_stieltjes_holomorphic
#print axioms OPICAWeightedSpectralMeasureIndependent.expected_arithmetic_stieltjes_sign_budget
#print axioms OPICAWeightedSpectralMeasureIndependent.expected_moment_is_source_norm
#print axioms OPICAWeightedSpectralMeasureIndependent.expected_real_point
#print axioms OPICAWeightedSpectralMeasureIndependent.expected_point_i
#print axioms OPICAWeightedSpectralMeasureIndependent.expected_offline_parameter
#print axioms OPICAWeightedSpectralMeasureIndependent.expected_critical_line_on_cut
