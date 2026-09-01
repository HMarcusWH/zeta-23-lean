import Zeta23.ExceptionalZero.TwoTranslateContraction

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Metric Set

/-!
# W1: recenter one negative pole-neutral Weil test into a strict finite aperture

W0 already supplies, from each hypothetical off-line zeta zero, one compact C² test
`h` with

* `paperFT h (±I/2) = 0`, and
* `Re (zetaZeroConfig.W h h) < 0`.

W1 is purely geometric/transport.  Compact closed support is enclosed in a symmetric
ball `(-r,r)`; right translation by `2r` moves the whole closed support into
`(r,3r)`, hence into the strict positive aperture `(0,4r)`.  Existing translation
theorems preserve C² regularity, compact support, the two Fourier zeros, and the
diagonal Weil value.
-/

/-- Exact closed-support transport for the repository convention
`translateRight h t x = h (x - t)`. -/
theorem tsupport_translateRight
    (h : ℝ → ℂ) (t : ℝ) :
    tsupport (translateRight h t) =
      (Homeomorph.subRight t) ⁻¹' tsupport h := by
  change tsupport (h ∘ Homeomorph.subRight t) =
    (Homeomorph.subRight t) ⁻¹' tsupport h
  exact tsupport_comp_eq_preimage h (Homeomorph.subRight t)

/-- A compact closed support fits inside a symmetric strict interval with positive radius. -/
theorem exists_pos_radius_tsupport_subset_Ioo
    {h : ℝ → ℂ}
    (hhc : HasCompactSupport h) :
    ∃ r : ℝ, 0 < r ∧ tsupport h ⊆ Ioo (-r) r := by
  obtain ⟨r, hr, hrs⟩ := hhc.isBounded.subset_ball_lt 0 0
  refine ⟨r, hr, ?_⟩
  intro x hx
  have hxball : x ∈ ball (0 : ℝ) r := hrs hx
  have habs : |x| < r := by
    simpa [Real.dist_eq] using hxball
  exact abs_lt.mp habs

/-- If the original closed support lies in `(-r,r)`, translating right by `2r`
puts it in the stronger interior margin `(r,3r)`. -/
theorem tsupport_translateRight_two_mul_subset_margin
    {h : ℝ → ℂ} {r : ℝ}
    (hs : tsupport h ⊆ Ioo (-r) r) :
    tsupport (translateRight h (2 * r)) ⊆ Ioo r (3 * r) := by
  rw [tsupport_translateRight]
  intro x hx
  have hx' : x - 2 * r ∈ tsupport h := by
    simpa using hx
  have hxr := hs hx'
  constructor <;> linarith [hxr.1, hxr.2]

/-- The explicit W1 geometry: choose a positive radius `r`, translate by `2r`,
and obtain both the stronger margin `(r,3r)` and the final aperture `(0,4r)`. -/
theorem exists_translateRight_strict_aperture
    {h : ℝ → ℂ}
    (hhc : HasCompactSupport h) :
    ∃ r : ℝ, 0 < r ∧
      tsupport (translateRight h (2 * r)) ⊆ Ioo r (3 * r) ∧
      tsupport (translateRight h (2 * r)) ⊆ Ioo 0 (4 * r) := by
  obtain ⟨r, hr, hs⟩ := exists_pos_radius_tsupport_subset_Ioo hhc
  have hmargin :
      tsupport (translateRight h (2 * r)) ⊆ Ioo r (3 * r) :=
    tsupport_translateRight_two_mul_subset_margin hs
  refine ⟨r, hr, hmargin, ?_⟩
  intro x hx
  have hxr := hmargin hx
  constructor <;> linarith [hr, hxr.1, hxr.2]

/-- Any Fourier zero is preserved under right translation. -/
theorem paperFT_translateRight_eq_zero_of_eq_zero
    (h : ℝ → ℂ) (t : ℝ) (z : ℂ)
    (hz : paperFT h z = 0) :
    paperFT (translateRight h t) z = 0 := by
  rw [paperFT_translateRight, hz, mul_zero]

/-- **W1, strong pointwise endpoint.** Every hypothetical off-line zero produces one
compact C² pole-neutral test supported strictly inside a positive finite aperture,
with an explicit positive interior margin and strictly negative genuine Weil self-value. -/
theorem exists_strictAperture_poleNeutral_negativeWeilTest_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ r : ℝ, 0 < r ∧ L = 4 * r ∧
        ∃ h : ℝ → ℂ,
          ContDiff ℝ 2 h ∧
          HasCompactSupport h ∧
          tsupport h ⊆ Ioo r (3 * r) ∧
          tsupport h ⊆ Ioo 0 L ∧
          paperFT h (I / 2) = 0 ∧
          paperFT h (-I / 2) = 0 ∧
          (zetaZeroConfig.W h h).re < 0 := by
  obtain ⟨h₀, hh₀, hhc₀, hp₀, hn₀, hneg₀⟩ :=
    exists_poleNeutral_negativeWeilTest_of_offLine_zero ρ₀ hoff
  obtain ⟨r, hr, hmargin, haperture⟩ :=
    exists_translateRight_strict_aperture hhc₀
  let h : ℝ → ℂ := translateRight h₀ (2 * r)
  let L : ℝ := 4 * r
  refine ⟨L, ?_, r, hr, rfl, h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [L]
    linarith
  · dsimp [h]
    exact contDiff_translateRight hh₀ (2 * r)
  · dsimp [h]
    exact hasCompactSupport_translateRight hhc₀ (2 * r)
  · simpa [h] using hmargin
  · simpa [h, L] using haperture
  · dsimp [h]
    exact paperFT_translateRight_eq_zero_of_eq_zero h₀ (2 * r) (I / 2) hp₀
  · dsimp [h]
    exact paperFT_translateRight_eq_zero_of_eq_zero h₀ (2 * r) (-I / 2) hn₀
  · dsimp [h]
    rw [W_translateRight_both]
    exact hneg₀

/-- Minimal strict-aperture W1 endpoint for downstream route composition. -/
theorem exists_strictAperture_negativeWeilTest_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ h : ℝ → ℂ,
        ContDiff ℝ 2 h ∧
        HasCompactSupport h ∧
        tsupport h ⊆ Ioo 0 L ∧
        (zetaZeroConfig.W h h).re < 0 := by
  obtain ⟨L, hL, r, _hr, _hLr, h, hh, hhc, _hmargin, hs, _hp, _hn, hneg⟩ :=
    exists_strictAperture_poleNeutral_negativeWeilTest_of_offLine_zero ρ₀ hoff
  exact ⟨L, hL, h, hh, hhc, hs, hneg⟩

/-- Existential logical wrapper used by the F1 roadmap. -/
theorem exists_strictAperture_negativeWeilTest_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ h : ℝ → ℂ,
        ContDiff ℝ 2 h ∧
        HasCompactSupport h ∧
        tsupport h ⊆ Ioo 0 L ∧
        (zetaZeroConfig.W h h).re < 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_strictAperture_negativeWeilTest_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero
