import Zeta23.CCM.WholeCellBiRegularCanonicalEnergy
import Zeta23.CCM.GlobalFirstBadParityBottomAlignment

noncomputable section

namespace Zeta23.CCM

open Complex Set

/-!
# PR #247 — canonical global-bottom residual state

The residual object keeps whole-cell provenance together with one retained
negative-energy certificate reselected at the true two-parity spectral bottom.

The branch is not stored as a naked trichotomy.  Its type records that the
selected certificate parity agrees with the branch that attained the global
bottom.  In the tied case we use the repository's canonical even selection.
-/

/-- Exact branch together with the parity actually selected by the aligned
retained certificate. -/
inductive GlobalBottomAlignedBranch
    (L : ℝ) (N : ℕ) (p : ReversalParity) : Type
  | evenStrict
      (hp : p = .even)
      (hstrict :
        parityRayleighBottom .even L (N + 1) <
          parityRayleighBottom .odd L (N + 1))
  | tieEven
      (hp : p = .even)
      (htie :
        parityRayleighBottom .even L (N + 1) =
          parityRayleighBottom .odd L (N + 1))
  | oddStrict
      (hp : p = .odd)
      (hstrict :
        parityRayleighBottom .odd L (N + 1) <
          parityRayleighBottom .even L (N + 1))

/-- Whole-cell retained provenance plus the exact globally aligned certificate. -/
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
        aligned.firstBad.L
        aligned.firstBad.Nstar
  global_neg :
    globalParitySuccessorBottom
        aligned.firstBad.L
        aligned.firstBad.Nstar < 0
  branch :
    GlobalBottomAlignedBranch
      aligned.firstBad.L
      aligned.firstBad.Nstar
      aligned.firstBad.p

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
  · obtain ⟨e, hL, hN, hp, hlam⟩ :=
      exists_globalBottomAligned_negativeEnergyCertificate_even
        c.retained hle
    have hlamGlobal :
        e.lam = globalParitySuccessorBottom e.firstBad.L e.firstBad.Nstar := by
      rw [hlam, hL, hN, globalParitySuccessorBottom, min_eq_left hle]
    have hglobal' :
        globalParitySuccessorBottom e.firstBad.L e.firstBad.Nstar < 0 := by
      simpa [hL, hN] using hglobal
    rcases lt_or_eq_of_le hle with hstrict | htie
    · refine ⟨{
        whole := c
        aligned := e
        same_L := hL
        same_N := hN
        aligned_lam_is_global := hlamGlobal
        global_neg := hglobal'
        branch := .evenStrict hp ?_
      }, rfl⟩
      simpa [hL, hN] using hstrict
    · refine ⟨{
        whole := c
        aligned := e
        same_L := hL
        same_N := hN
        aligned_lam_is_global := hlamGlobal
        global_neg := hglobal'
        branch := .tieEven hp ?_
      }, rfl⟩
      simpa [hL, hN] using htie
  · have hodd :
      parityRayleighBottom .odd fb.L (fb.Nstar + 1) <
        parityRayleighBottom .even fb.L (fb.Nstar + 1) :=
      lt_of_not_ge hle
    obtain ⟨e, hL, hN, hp, hlam⟩ :=
      exists_globalBottomAligned_negativeEnergyCertificate_odd
        c.retained hodd
    have hlamGlobal :
        e.lam = globalParitySuccessorBottom e.firstBad.L e.firstBad.Nstar := by
      rw [hlam, hL, hN, globalParitySuccessorBottom,
        min_eq_right (le_of_lt hodd)]
    have hglobal' :
        globalParitySuccessorBottom e.firstBad.L e.firstBad.Nstar < 0 := by
      simpa [hL, hN] using hglobal
    refine ⟨{
      whole := c
      aligned := e
      same_L := hL
      same_N := hN
      aligned_lam_is_global := hlamGlobal
      global_neg := hglobal'
      branch := .oddStrict hp ?_
    }, rfl⟩
    simpa [hL, hN] using hodd

/-- The residual state's aligned certificate stores a strictly negative shift. -/
theorem GlobalBottomResidualState.aligned_lam_neg
    {Q : ℕ}
    (s : GlobalBottomResidualState Q) :
    s.aligned.lam < 0 := by
  rw [s.aligned_lam_is_global]
  exact s.global_neg

/-- The branch can never disagree with the selected parity. -/
theorem GlobalBottomResidualState.selectedParity_spec
    {Q : ℕ}
    (s : GlobalBottomResidualState Q) :
    (s.aligned.firstBad.p = .even ∧
        (parityRayleighBottom .even s.aligned.firstBad.L
            (s.aligned.firstBad.Nstar + 1) ≤
          parityRayleighBottom .odd s.aligned.firstBad.L
            (s.aligned.firstBad.Nstar + 1))) ∨
      (s.aligned.firstBad.p = .odd ∧
        parityRayleighBottom .odd s.aligned.firstBad.L
            (s.aligned.firstBad.Nstar + 1) <
          parityRayleighBottom .even s.aligned.firstBad.L
            (s.aligned.firstBad.Nstar + 1)) := by
  cases s.branch with
  | evenStrict hp hstrict =>
      exact Or.inl ⟨hp, le_of_lt hstrict⟩
  | tieEven hp htie =>
      exact Or.inl ⟨hp, le_of_eq htie⟩
  | oddStrict hp hstrict =>
      exact Or.inr ⟨hp, hstrict⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.GlobalBottomResidualState
#print axioms Zeta23.CCM.exists_globalBottomResidualState_of_wholeCell
#print axioms Zeta23.CCM.GlobalBottomResidualState.aligned_lam_neg
#print axioms Zeta23.CCM.GlobalBottomResidualState.selectedParity_spec
