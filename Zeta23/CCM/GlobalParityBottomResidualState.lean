import Zeta23.CCM.WholeCellBiRegularCanonicalEnergy
import Zeta23.CCM.GlobalFirstBadParityBottomAlignment

noncomputable section

namespace Zeta23.CCM

open Complex Set

/-!
# PR #247 — canonical global-bottom residual state

This is the finite object left after global-bottom reparameterization.  It does
not assert a contradiction.  It packages whole-cell provenance, an aligned
negative-energy certificate at the true two-parity ground value, and the exact
strict-even / tie / strict-odd case split.

The object is deliberately RH-neutral and lives in CCM rather than the
ExceptionalZero namespace.  A hypothetical off-line zero will later be shown
to generate such states at arbitrarily large aperture.
-/

structure GlobalBottomResidualState (Q : ℕ) where
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
    parityRayleighBottom .even
          whole.retained.energy.firstBad.L
          (whole.retained.energy.firstBad.Nstar + 1) <
        parityRayleighBottom .odd
          whole.retained.energy.firstBad.L
          (whole.retained.energy.firstBad.Nstar + 1) ∨
      parityRayleighBottom .even
          whole.retained.energy.firstBad.L
          (whole.retained.energy.firstBad.Nstar + 1) =
        parityRayleighBottom .odd
          whole.retained.energy.firstBad.L
          (whole.retained.energy.firstBad.Nstar + 1) ∨
      parityRayleighBottom .odd
          whole.retained.energy.firstBad.L
          (whole.retained.energy.firstBad.Nstar + 1) <
        parityRayleighBottom .even
          whole.retained.energy.firstBad.L
          (whole.retained.energy.firstBad.Nstar + 1)

/-- Every whole-cell bi-regular state admits the canonical global-bottom
residual packaging. -/
theorem exists_globalBottomResidualState_of_wholeCell
    {Q : ℕ}
    (c : WholeCellBiRegularNegativeEnergyCertificate Q) :
    ∃ s : GlobalBottomResidualState Q,
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
        same_L := by simpa [fb] using hL
        same_N := by simpa [fb] using hN
        aligned_lam_is_global := by simpa [fb] using hlamGlobal
        global_neg := by simpa [fb] using hglobal
        branch := Or.inl hstrict
      }, rfl⟩
    · refine ⟨{
        whole := c
        aligned := e
        same_L := by simpa [fb] using hL
        same_N := by simpa [fb] using hN
        aligned_lam_is_global := by simpa [fb] using hlamGlobal
        global_neg := by simpa [fb] using hglobal
        branch := Or.inr (Or.inl htie)
      }, rfl⟩
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
      same_L := by simpa [fb] using hL
      same_N := by simpa [fb] using hN
      aligned_lam_is_global := by simpa [fb] using hlamGlobal
      global_neg := by simpa [fb] using hglobal
      branch := Or.inr (Or.inr hodd)
    }, rfl⟩

/-- The residual state's aligned certificate stores a strictly negative shift. -/
theorem GlobalBottomResidualState.aligned_lam_neg
    {Q : ℕ}
    (s : GlobalBottomResidualState Q) :
    s.aligned.lam < 0 := by
  rw [s.aligned_lam_is_global]
  exact s.global_neg

end Zeta23.CCM

#print axioms Zeta23.CCM.GlobalBottomResidualState
#print axioms Zeta23.CCM.exists_globalBottomResidualState_of_wholeCell
#print axioms Zeta23.CCM.GlobalBottomResidualState.aligned_lam_neg
