import Zeta23.OPICAFollowup.SquareDefect
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap ComplexConjugate
open Zeta23.OPICAFollowup
variable {h : ℝ → ℂ} {A : ℂ}
-- (1) the square is not self-dual: the defect is not zero
theorem bad_selfdual (hev : ∀ x, h (-x) = h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h = h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (φ : 𝓢(ℝ, ℂ)) :
    squareGapMeasure h A (𝓕 φ) - squareGapMeasure h A φ = 0 :=
  (square_fourier_defect hev hcont hint hL2 hsd hvan hpl).2.2.2.2.2.2.2 φ
-- (2) the defect is h ⋆ conj h - |h|², not h ⋆ h - |h|²: the origin value is ‖h‖² - |A|², not ‖h‖²
theorem bad_origin_value (hev : ∀ x, h (-x) = h x) (hcont : Continuous h) (hL2 : MemLp h 2)
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    squareDualityDefect h 0 = ((∫ x, ‖h x‖ ^ 2 : ℝ) : ℂ) :=
  (square_defect_origin_positive hev hcont hL2 hpl hne).1
-- (3) the origin value is positive, not negative
theorem bad_origin_sign (hev : ∀ x, h (-x) = h x) (hcont : Continuous h) (hL2 : MemLp h 2)
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    (∫ x, ‖h x‖ ^ 2) - ‖A‖ ^ 2 < 0 :=
  (square_defect_origin_positive hev hcont hL2 hpl hne).2.1
-- (4) the plateau bound is |A|², not 2|A|²
theorem bad_plateau_bound (hev : ∀ x, h (-x) = h x) (hcont : Continuous h) (hL2 : MemLp h 2)
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) (hA : A ≠ 0) :
    2 * ‖A‖ ^ 2 ≤ (∫ x, ‖h x‖ ^ 2) - ‖A‖ ^ 2 :=
  (square_defect_origin_positive hev hcont hL2 hpl hne).2.2.1 hA
-- (5) a lattice correction cannot repair the defect
theorem bad_lattice_repair (hev : ∀ x, h (-x) = h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h = h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    ∃ c : ℤ → ℂ, TemperedLatticeWeights c ∧ ∀ φ : 𝓢(ℝ, ℂ),
      squareGapMeasure h A (𝓕 φ) + latticePairing c (𝓕 φ) = squareGapMeasure h A φ + latticePairing c φ :=
  square_no_lattice_repair hev hcont hint hL2 hsd hvan hpl hne
-- (6) the projection is τ + d/2, not τ + d
theorem bad_projection_weight (hev : ∀ x, h (-x) = h x) (hcont : Continuous h)
    (hint : Integrable h) (hL2 : MemLp h 2) (hsd : 𝓕 h = h)
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) (φ : 𝓢(ℝ, ℂ)) :
    Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A) φ =
      squareGapMeasure h A φ + ∫ x, squareDualityDefect h x * φ x :=
  (square_selfdual_projection_fills_gap hev hcont hint hL2 hsd hpl hne).2.1 φ
-- (7) the projection's density in the gap is positive, not negative
theorem bad_gap_sign (hev : ∀ x, h (-x) = h x) (hcont : Continuous h)
    (hint : Integrable h) (hL2 : MemLp h 2) (hsd : 𝓕 h = h)
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (∀ x ∈ Ioo (-ε) ε, (squareDualityDefect h x).re < 0 ∧ (squareDualityDefect h x).im = 0) ∧
      ∀ φ : 𝓢(ℝ, ℂ), tsupport φ ⊆ Ioo (-ε) ε →
        Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A) φ =
          ∫ x, (squareDualityDefect h x / 2) * φ x :=
  (square_selfdual_projection_fills_gap hev hcont hint hL2 hsd hpl hne).2.2
-- (8) without self-duality of h the defect identity is not available
theorem bad_no_selfdual (hev : ∀ x, h (-x) = h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (φ : 𝓢(ℝ, ℂ)) :
    squareGapMeasure h A (𝓕 φ) - squareGapMeasure h A φ = ∫ x, squareDualityDefect h x * φ x :=
  (square_fourier_defect hev hcont hint hL2 hvan hpl).2.2.2.2.2.2.2 φ
