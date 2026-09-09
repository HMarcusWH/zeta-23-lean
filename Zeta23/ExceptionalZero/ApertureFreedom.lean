import Zeta23.ExceptionalZero.FiniteNegativeObstruction
import Zeta23.CCM.GlobalFirstBad

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Function MeasureTheory Real Set

/-!
# FIRST-BAD-RIGIDITY-E4-A4R0: aperture freedom

The existing W1 theorem produces, from an off-line zero, one fixed compact C²
negative Weil test whose closed support lies in a strict positive interval.
The finite approximation theorem can therefore be rerun at every larger
aperture.  This strengthens F1 from existence of one bad aperture to eventual
badness at every sufficiently large aperture.

No continuity of the finite canonical matrix in `L`, no regular-aperture
selection, no determinant nonvanishing, no positivity theorem, and no RH
claim is used here.
-/

/-- Every hypothetical off-line zeta zero forces a finite canonical negative
obstruction at every sufficiently large aperture.  The finite size and vector
may depend on the chosen aperture. -/
theorem
    eventually_all_apertures_have_negativeCanonicalSourceWitness_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ L : ℝ, L₀ < L →
        ∃ N : ℕ, 1 ≤ N ∧
          ∃ u : Fin (2 * N + 1) → ℂ,
            Zeta23.CCM.BoundaryFlatCoefficients N u ∧
            (Zeta23.CCM.quadraticForm
              (Zeta23.CCM.canonicalSourceMatrix L N) u).re < 0 := by
  obtain ⟨_L, _hL, r, hr, _hLr, h, hh, hhc, hmargin, _hs,
      _hp, _hn, hneg⟩ :=
    exists_strictAperture_poleNeutral_negativeWeilTest_of_offLine_zero
      ρ₀ hoff
  refine ⟨4 * r, by positivity, ?_⟩
  intro L hLbig
  have hL : 0 < L := by nlinarith
  have hs : tsupport h ⊆ Ioo 0 L := by
    intro x hx
    have hxm := hmargin hx
    constructor
    · exact lt_trans hr hxm.1
    · have h34 : 3 * r < 4 * r := by nlinarith [hr]
      exact lt_trans hxm.2 (lt_trans h34 hLbig)
  obtain ⟨N, hN, u, hflat, hfiniteNeg⟩ :=
    exists_boundaryFlatFinite_negativeW_of_strictAperture
      hL hh hhc hs hneg
  refine ⟨N, hN, u, hflat, ?_⟩
  rw [← zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm
    N u hL hflat]
  exact hfiniteNeg

/-- Existential wrapper of the eventual-aperture finite negative obstruction. -/
theorem
    eventually_all_apertures_have_negativeCanonicalSourceWitness_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ L : ℝ, L₀ < L →
        ∃ N : ℕ, 1 ≤ N ∧
          ∃ u : Fin (2 * N + 1) → ℂ,
            Zeta23.CCM.BoundaryFlatCoefficients N u ∧
            (Zeta23.CCM.quadraticForm
              (Zeta23.CCM.canonicalSourceMatrix L N) u).re < 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    eventually_all_apertures_have_negativeCanonicalSourceWitness_of_offLine_zero
      ρ₀ hρ₀

/-- Every sufficiently large aperture is globally parity-bad at some finite
size.  This is a direct packaging of the preceding theorem through the exact
boundary-flat subspace and parity decomposition. -/
theorem
    eventually_all_apertures_have_anyParityBad_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ L : ℝ, L₀ < L →
        ∃ N : ℕ, Zeta23.CCM.AnyParityBad L N := by
  obtain ⟨L₀, hL₀, hnegAll⟩ :=
    eventually_all_apertures_have_negativeCanonicalSourceWitness_of_offLine_zero
      ρ₀ hoff
  refine ⟨L₀, hL₀, ?_⟩
  intro L hLbig
  obtain ⟨N, _hN, u, hflat, hneg⟩ := hnegAll L hLbig
  have hmem : u ∈ Zeta23.CCM.boundaryFlatSubspace N :=
    (Zeta23.CCM.mem_boundaryFlatSubspace_iff N u).2 hflat
  exact ⟨N, Zeta23.CCM.anyParityBad_of_negative hmem hneg⟩

/-- At every sufficiently large aperture forced by an off-line zero, the
repository can freshly select a least globally bad finite size. -/
theorem
    eventually_all_apertures_have_globalFirstBad_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ L : ℝ, L₀ < L →
        ∃ Nstar : ℕ,
          2 ≤ Nstar ∧
          Zeta23.CCM.AnyParityBad L Nstar ∧
          ∀ N : ℕ, N < Nstar → ¬ Zeta23.CCM.AnyParityBad L N := by
  obtain ⟨L₀, hL₀, hbadAll⟩ :=
    eventually_all_apertures_have_anyParityBad_of_offLine_zero ρ₀ hoff
  refine ⟨L₀, hL₀, ?_⟩
  intro L hLbig
  obtain ⟨N, hbad⟩ := hbadAll L hLbig
  exact Zeta23.CCM.exists_least_anyParityBad_two_le L ⟨N, hbad⟩

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.eventually_all_apertures_have_negativeCanonicalSourceWitness_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.eventually_all_apertures_have_anyParityBad_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.eventually_all_apertures_have_globalFirstBad_of_offLine_zero