import Zeta23.OPICAFollowup.SquareDefect

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.square_fourier_defect`,
`Zeta23.OPICAFollowup.square_defect_origin_positive`, `Zeta23.OPICAFollowup.square_no_lattice_repair`
and `Zeta23.OPICAFollowup.square_selfdual_projection_fills_gap` (R2-S3).

Definition audits pin τ_h = |A - h|² dx - |A|² Σ_(n ≠ 0) δ_n, the defect d = h ⋆ conj h - |h|²,
the lattice correction pairing and the Fourier action on functionals; the projection is the
parent `Zeta23.OPICA.involutionSelfdualProjection`. All four roots are restated in full. Domain
consumers instantiate them at the actual zero profile h = h_κ, A = 1, of an actual zero: every
hypothesis (evenness, continuity, L¹ ∩ L², ordinary self-duality, vanishing at infinity, plateau,
nonvanishing) is discharged from Stage 9, so the generic theorems apply to the actual square
construction. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap ComplexConjugate
open Zeta23.OPICAFollowup
namespace OPICASquareDefectIndependent

/-! ### Definition audits -/

theorem audit_squareGapMeasure (h : ℝ → ℂ) (A : ℂ) (φ : 𝓢(ℝ, ℂ)) : squareGapMeasure h A φ =
    (∫ x, ((‖A - h x‖ ^ 2 : ℝ) : ℂ) * φ x) - ((‖A‖ ^ 2 : ℝ) : ℂ) * ∑' n : ℤ, (if n = 0 then 0 else φ n) :=
  rfl

theorem audit_squareDualityDefect (h : ℝ → ℂ) (x : ℝ) :
    squareDualityDefect h x = (∫ y, h y * conj (h (x - y))) - h x * conj (h x) := rfl

theorem audit_projection (T : 𝓢(ℝ, ℂ) → ℂ) :
    Zeta23.OPICA.involutionSelfdualProjection fourierFunctional T = (2 : ℂ)⁻¹ • (T + fun φ => T (𝓕 φ)) :=
  rfl

/-! ### Restated roots -/

variable {h : ℝ → ℂ} {A : ℂ}

theorem expected_square_fourier_defect (hev : ∀ x, h (-x) = h x) (hcont : Continuous h)
    (hint : Integrable h) (hL2 : MemLp h 2) (hsd : 𝓕 h = h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x, |x| ≤ 1 → h x = A) :
    (∀ φ : 𝓢(ℝ, ℂ), tsupport φ ⊆ Ioo (-1) 1 → squareGapMeasure h A φ = 0) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (∀ x, 0 ≤ (φ x).re ∧ (φ x).im = 0) → (∀ n : ℤ, φ n = 0) →
      0 ≤ (squareGapMeasure h A φ).re) ∧
    (∃ M : ℝ, ∀ x, ‖A - h x‖ ^ 2 ≤ M) ∧
    Continuous (squareDualityDefect h) ∧ Tendsto (squareDualityDefect h) (cocompact ℝ) (𝓝 0) ∧
    (∀ x, (squareDualityDefect h x).im = 0) ∧
    (∀ x, squareDualityDefect h x = 𝓕 (fun y => h y * conj (h y)) x - h x * conj (h x)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), squareGapMeasure h A (𝓕 φ) - squareGapMeasure h A φ = ∫ x, squareDualityDefect h x * φ x) :=
  square_fourier_defect hev hcont hint hL2 hsd hvan hpl

theorem expected_square_defect_origin_positive (hev : ∀ x, h (-x) = h x) (hcont : Continuous h)
    (hL2 : MemLp h 2) (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    squareDualityDefect h 0 = (((∫ x, ‖h x‖ ^ 2) - ‖A‖ ^ 2 : ℝ) : ℂ) ∧
    0 < (∫ x, ‖h x‖ ^ 2) - ‖A‖ ^ 2 ∧
    (A ≠ 0 → ‖A‖ ^ 2 ≤ (∫ x, ‖h x‖ ^ 2) - ‖A‖ ^ 2) ∧
    (A = 0 → 0 < ∫ x, ‖h x‖ ^ 2) :=
  square_defect_origin_positive hev hcont hL2 hpl hne

theorem expected_square_no_lattice_repair (hev : ∀ x, h (-x) = h x) (hcont : Continuous h)
    (hint : Integrable h) (hL2 : MemLp h 2) (hsd : 𝓕 h = h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    ¬ ∃ c : ℤ → ℂ, TemperedLatticeWeights c ∧ ∀ φ : 𝓢(ℝ, ℂ),
      squareGapMeasure h A (𝓕 φ) + latticePairing c (𝓕 φ) = squareGapMeasure h A φ + latticePairing c φ :=
  square_no_lattice_repair hev hcont hint hL2 hsd hvan hpl hne

theorem expected_square_selfdual_projection_fills_gap (hev : ∀ x, h (-x) = h x) (hcont : Continuous h)
    (hint : Integrable h) (hL2 : MemLp h 2) (hsd : 𝓕 h = h)
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    fourierFunctional (Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A)) =
      Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A) ∧
    (∀ φ : 𝓢(ℝ, ℂ), Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A) φ =
      squareGapMeasure h A φ + (1 / 2) * ∫ x, squareDualityDefect h x * φ x) ∧
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (∀ x ∈ Ioo (-ε) ε, 0 < (squareDualityDefect h x).re ∧ (squareDualityDefect h x).im = 0) ∧
      ∀ φ : 𝓢(ℝ, ℂ), tsupport φ ⊆ Ioo (-ε) ε →
        Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A) φ =
          ∫ x, (squareDualityDefect h x / 2) * φ x :=
  square_selfdual_projection_fills_gap hev hcont hint hL2 hsd hpl hne

/-! ### Actual domain: the zero profile of an actual zero -/

lemma zeroProfile_vanishing {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    Tendsto (zeroProfile ρ) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := zeroProfile_norm_le hz h0 h1
  have hlim : Tendsto (fun x : ℝ => K * (1 + x ^ 2)⁻¹) (cocompact ℝ) (𝓝 (K * 0)) := by
    refine (tendsto_inv_atTop_zero.comp ?_).const_mul K
    refine tendsto_atTop_add_const_left _ _ ?_
    have hn := (tendsto_pow_atTop (two_ne_zero : (2 : ℕ) ≠ 0)).comp (tendsto_norm_cocompact_atTop (E := ℝ))
    refine hn.congr fun x => ?_
    simp [Real.norm_eq_abs, sq_abs]
  rw [mul_zero] at hlim
  exact squeeze_zero_norm (fun x => hK x) hlim

lemma zeroProfile_ne_zero (ρ : ℂ) : zeroProfile ρ ≠ 0 := fun h => by
  have := congrFun h 0
  rw [zeroProfile_eq_one ρ (by simp)] at this
  exact one_ne_zero this

/-- The actual square construction at an actual zero: all four roots hold for h = h_κ, A = 1; the
defect at the origin is d(0) = ‖h_κ‖₂² - 1 ≥ 1, and no lattice correction repairs it. -/
theorem expected_actual_square {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (∀ φ : 𝓢(ℝ, ℂ), squareGapMeasure (zeroProfile ρ) 1 (𝓕 φ) - squareGapMeasure (zeroProfile ρ) 1 φ =
      ∫ x, squareDualityDefect (zeroProfile ρ) x * φ x) ∧
    1 ≤ (∫ x, ‖zeroProfile ρ x‖ ^ 2) - 1 ∧
    squareDualityDefect (zeroProfile ρ) 0 = (((∫ x, ‖zeroProfile ρ x‖ ^ 2) - 1 : ℝ) : ℂ) ∧
    (¬ ∃ c : ℤ → ℂ, TemperedLatticeWeights c ∧ ∀ φ : 𝓢(ℝ, ℂ),
      squareGapMeasure (zeroProfile ρ) 1 (𝓕 φ) + latticePairing c (𝓕 φ) =
        squareGapMeasure (zeroProfile ρ) 1 φ + latticePairing c φ) ∧
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x ∈ Ioo (-ε) ε, 0 < (squareDualityDefect (zeroProfile ρ) x).re := by
  have hev := zeroProfile_neg ρ
  have hcont := continuous_zeroProfile ρ
  have hint := integrable_zeroProfile hz h0 h1
  have hL2 := memLp_two_zeroProfile hz h0 h1
  have hsd := fourier_zeroProfile hz h0 h1
  have hvan := zeroProfile_vanishing hz h0 h1
  have hpl : ∀ x, |x| ≤ 1 → zeroProfile ρ x = 1 := fun x hx => zeroProfile_eq_one ρ hx
  have hne := zeroProfile_ne_zero ρ
  obtain ⟨hd0, -, hge, -⟩ := square_defect_origin_positive hev hcont hL2 hpl hne
  obtain ⟨-, -, ε, hε0, hε1, hεx, -⟩ := square_selfdual_projection_fills_gap hev hcont hint hL2 hsd hpl hne
  refine ⟨(square_fourier_defect hev hcont hint hL2 hsd hvan hpl).2.2.2.2.2.2.2, ?_, ?_,
    square_no_lattice_repair hev hcont hint hL2 hsd hvan hpl hne, ε, hε0, hε1, fun x hx => (hεx x hx).1⟩
  · simpa using hge one_ne_zero
  · simpa using hd0

end OPICASquareDefectIndependent
#print axioms Zeta23.OPICAFollowup.square_fourier_defect
#print axioms Zeta23.OPICAFollowup.square_defect_origin_positive
#print axioms Zeta23.OPICAFollowup.square_no_lattice_repair
#print axioms Zeta23.OPICAFollowup.square_selfdual_projection_fills_gap
#print axioms OPICASquareDefectIndependent.audit_projection
#print axioms OPICASquareDefectIndependent.expected_square_fourier_defect
#print axioms OPICASquareDefectIndependent.expected_square_defect_origin_positive
#print axioms OPICASquareDefectIndependent.expected_square_no_lattice_repair
#print axioms OPICASquareDefectIndependent.expected_square_selfdual_projection_fills_gap
#print axioms OPICASquareDefectIndependent.expected_actual_square
