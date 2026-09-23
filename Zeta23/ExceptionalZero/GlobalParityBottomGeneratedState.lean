import Zeta23.ExceptionalZero.OffLineGeneratedRetainedFamily
import Zeta23.CCM.GlobalFirstBadParityBottomAlignment
import Zeta23.CCM.GlobalParityBottomResidualState

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Set
open Zeta23.CCM

/-!
# PR #247 — generated global-bottom state

This module threads the off-line-zero generated whole-cell certificate through
the new global-bottom alignment layer.  The result is not merely the tautological
trichotomy of two real numbers: it retains the exact generated whole-cell
provenance and a negative-energy certificate whose stored shift is the true
minimum parity ground energy.

No branch is excluded here.  The three constructors are an exact case split
for downstream strict-even, strict-odd, and tie analysis.
-/

/-- Exact branch of the two successor parity ground levels. -/
inductive GlobalParityBottomBranch (L : ℝ) (N : ℕ) : Type
  | evenStrict
      (h :
        parityRayleighBottom .even L (N + 1) <
          parityRayleighBottom .odd L (N + 1))
  | tie
      (h :
        parityRayleighBottom .even L (N + 1) =
          parityRayleighBottom .odd L (N + 1))
  | oddStrict
      (h :
        parityRayleighBottom .odd L (N + 1) <
          parityRayleighBottom .even L (N + 1))

/-- A whole-cell off-line-generated state together with a certificate reselected
at the actual global parity bottom. -/
structure GeneratedGlobalParityBottomState (Q : ℕ) where
  whole : WholeCellBiRegularNegativeEnergyCertificate Q
  aligned : RegularCellMinimalNegativeEnergyCertificate Q
  same_L :
    aligned.firstBad.L = whole.retained.energy.firstBad.L
  same_N :
    aligned.firstBad.Nstar = whole.retained.energy.firstBad.Nstar
  aligned_lam_is_global :
    aligned.lam =
      globalParitySuccessorBottom
        whole.retained.energy.firstBad.L
        whole.retained.energy.firstBad.Nstar
  global_neg :
    globalParitySuccessorBottom
        whole.retained.energy.firstBad.L
        whole.retained.energy.firstBad.Nstar < 0
  branch :
    GlobalParityBottomBranch
      whole.retained.energy.firstBad.L
      whole.retained.energy.firstBad.Nstar

/-- Any whole-cell bi-regular retained state can be aligned with its true
two-parity spectral bottom without changing aperture or predecessor size. -/
theorem exists_generatedGlobalParityBottomState
    {Q : ℕ}
    (c : WholeCellBiRegularNegativeEnergyCertificate Q) :
    ∃ s : GeneratedGlobalParityBottomState Q,
      s.whole = c := by
  let fb := c.retained.energy.firstBad
  have hglobal :
      globalParitySuccessorBottom fb.L fb.Nstar < 0 :=
    fb.globalParityBottom_neg
  by_cases hle :
      parityRayleighBottom .even fb.L (fb.Nstar + 1) ≤
        parityRayleighBottom .odd fb.L (fb.Nstar + 1)
  · obtain ⟨e, hL, hN, _hp, hlam⟩ :=
      exists_globalBottomAligned_negativeEnergyCertificate_even
        c.retained hle
    have hlamGlobal :
        e.lam = globalParitySuccessorBottom fb.L fb.Nstar := by
      rw [hlam, globalParitySuccessorBottom, min_eq_left hle]
    rcases lt_or_eq_of_le hle with hstrict | htie
    · refine ⟨{
        whole := c
        aligned := e
        same_L := ?_
        same_N := ?_
        aligned_lam_is_global := ?_
        global_neg := ?_
        branch := .evenStrict hstrict
      }, rfl⟩
      · simpa [fb] using hL
      · simpa [fb] using hN
      · simpa [fb] using hlamGlobal
      · simpa [fb] using hglobal
    · refine ⟨{
        whole := c
        aligned := e
        same_L := ?_
        same_N := ?_
        aligned_lam_is_global := ?_
        global_neg := ?_
        branch := .tie htie
      }, rfl⟩
      · simpa [fb] using hL
      · simpa [fb] using hN
      · simpa [fb] using hlamGlobal
      · simpa [fb] using hglobal
  · have hodd :
      parityRayleighBottom .odd fb.L (fb.Nstar + 1) <
        parityRayleighBottom .even fb.L (fb.Nstar + 1) :=
      lt_of_not_ge hle
    obtain ⟨e, hL, hN, _hp, hlam⟩ :=
      exists_globalBottomAligned_negativeEnergyCertificate_odd
        c.retained hodd
    have hlamGlobal :
        e.lam = globalParitySuccessorBottom fb.L fb.Nstar := by
      rw [hlam, globalParitySuccessorBottom,
        min_eq_right (le_of_lt hodd)]
    refine ⟨{
      whole := c
      aligned := e
      same_L := ?_
      same_N := ?_
      aligned_lam_is_global := ?_
      global_neg := ?_
      branch := .oddStrict hodd
    }, rfl⟩
    · simpa [fb] using hL
    · simpa [fb] using hN
    · simpa [fb] using hlamGlobal
    · simpa [fb] using hglobal

/-- A hypothetical off-line zero produces aligned global-bottom states at
arbitrarily large retained apertures. -/
theorem
    exists_arbitrarilyLarge_generatedGlobalParityBottomState_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2)
    (A : ℝ) :
    ∃ Q : ℕ,
      ∃ s : GeneratedGlobalParityBottomState Q,
        A < s.whole.retained.energy.firstBad.L := by
  obtain ⟨Q, c, hlarge⟩ :=
    exists_arbitrarilyLarge_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero
      ρ₀ hoff A
  obtain ⟨s, rfl⟩ := exists_generatedGlobalParityBottomState c
  exact ⟨Q, s, hlarge⟩

/-- Existential off-line-zero wrapper. -/
theorem
    exists_arbitrarilyLarge_generatedGlobalParityBottomState_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2)
    (A : ℝ) :
    ∃ Q : ℕ,
      ∃ s : GeneratedGlobalParityBottomState Q,
        A < s.whole.retained.energy.firstBad.L := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_arbitrarilyLarge_generatedGlobalParityBottomState_of_offLine_zero
      ρ₀ hρ₀ A


/-- A hypothetical off-line zero produces the CCM-level residual object at
arbitrarily large aperture.  This is the exact bridge from zeta-side
provenance into the RH-neutral finite residual state. -/
theorem
    exists_arbitrarilyLarge_globalBottomResidualState_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2)
    (A : ℝ) :
    ∃ Q : ℕ,
      ∃ s : GlobalBottomResidualState Q,
        A < s.whole.retained.energy.firstBad.L := by
  obtain ⟨Q, c, hlarge⟩ :=
    exists_arbitrarilyLarge_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero
      ρ₀ hoff A
  obtain ⟨s, rfl⟩ :=
    exists_globalBottomResidualState_of_wholeCell c
  exact ⟨Q, s, hlarge⟩

/-- Existential off-line-zero wrapper for the residual state. -/
theorem
    exists_arbitrarilyLarge_globalBottomResidualState_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2)
    (A : ℝ) :
    ∃ Q : ℕ,
      ∃ s : GlobalBottomResidualState Q,
        A < s.whole.retained.energy.firstBad.L := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_arbitrarilyLarge_globalBottomResidualState_of_offLine_zero
      ρ₀ hρ₀ A

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_generatedGlobalParityBottomState
#print axioms Zeta23.ExceptionalZero.exists_arbitrarilyLarge_generatedGlobalParityBottomState_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_arbitrarilyLarge_generatedGlobalParityBottomState_of_exists_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_arbitrarilyLarge_globalBottomResidualState_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_arbitrarilyLarge_globalBottomResidualState_of_exists_offLine_zero
