import Zeta23.CCM.LiftedPredecessorRegularity
import Zeta23.CCM.CanonicalApertureContinuity
import Zeta23.CCM.GlobalFirstBad

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4R5: cell-minimal regular first bad

A fixed-aperture least bad size cannot be transported after moving the aperture
to a nearby regular point.  The correct minimum is therefore taken over the
whole physical prime-cutoff cell.

This file formalizes exactly that quantifier order, then composes the minimum
with fixed-cell strict-sign persistence and the analytic regular-aperture
selection theorem.  The same negative witness persists while the aperture is
moved to a point where the predecessor block is regular.

No source positivity, negative-root exclusion, finite-to-infinite closure, or
RH theorem is claimed here.
-/

/-- Size `K` is bad somewhere in the physical cutoff cell for `Q`. -/
def CellAnyParityBad (Q K : ℕ) : Prop :=
  ∃ L ∈ fixedCanonicalCutoffCell Q, AnyParityBad L K

/-- A nonempty cell-bad size set has a least size, automatically at least two. -/
theorem exists_least_cellAnyParityBad_two_le
    (Q : ℕ)
    (hex : ∃ K : ℕ, CellAnyParityBad Q K) :
    ∃ Kstar : ℕ,
      2 ≤ Kstar ∧
      CellAnyParityBad Q Kstar ∧
      ∀ K : ℕ, K < Kstar → ¬ CellAnyParityBad Q K := by
  classical
  let Kstar := Nat.find hex
  have hbad : CellAnyParityBad Q Kstar := Nat.find_spec hex
  obtain ⟨L, hLcell, hLbad⟩ := hbad
  refine ⟨Kstar, two_le_of_anyParityBad hLbad, ⟨L, hLcell, hLbad⟩, ?_⟩
  intro K hK
  exact Nat.find_min hex hK

/-- Cell-minimality is uniform in the aperture: every smaller size is good at
every point of the same cutoff cell. -/
theorem not_anyParityBad_of_lt_cellMinimal
    {Q Kstar : ℕ}
    (hmin : ∀ K : ℕ, K < Kstar → ¬ CellAnyParityBad Q K)
    {M : ℕ} (hM : M < Kstar)
    {L : ℝ} (hL : L ∈ fixedCanonicalCutoffCell Q) :
    ¬ AnyParityBad L M := by
  intro hbad
  exact (hmin M hM) ⟨L, hL, hbad⟩

/-- Headline composition theorem: if a cutoff cell is bad at some finite size,
then it contains a *regular* aperture at a cell-minimal first-bad size.

The output aperture may differ from the aperture that first witnessed
cell-badness, but the exact same negative vector is persisted to it.  Because
the minimum was taken over the whole cell, all smaller sizes remain good after
this move. -/
theorem exists_regular_cellMinimal_firstBad
    (Q : ℕ) (hQ : 1 ≤ Q)
    (hex : ∃ K : ℕ, CellAnyParityBad Q K) :
    ∃ Kstar Nstar : ℕ,
      ∃ L : ℝ,
        ∃ p : ReversalParity,
          2 ≤ Kstar ∧
          1 ≤ Nstar ∧
          Nstar + 1 = Kstar ∧
          L ∈ fixedCanonicalCutoffCell Q ∧
          ParityBad p L Kstar ∧
          (∀ M : ℕ, M < Kstar → ¬ AnyParityBad L M) ∧
          IntrinsicPredecessorRegular p L Nstar := by
  obtain ⟨Kstar, hKtwo, hcellBad, hminCell⟩ :=
    exists_least_cellAnyParityBad_two_le Q hex
  obtain ⟨L₁, hL₁cell, hbadEither⟩ := hcellBad
  rcases hbadEither with hbad | hbad
  · let p : ReversalParity := .even
    obtain ⟨u, hune, humem, hneg⟩ := hbad
    obtain ⟨J, hJopen, hL₁J, hJcell, hJneg⟩ :=
      exists_open_fixedCell_negativeCanonicalSourceWitness_persistence
        Q Kstar hQ u hL₁cell hneg
    let Nstar := Kstar - 1
    have hNstar : 1 ≤ Nstar := by
      dsimp [Nstar]
      omega
    have hsucc : Nstar + 1 = Kstar := by
      dsimp [Nstar]
      omega
    obtain ⟨L, hLJ, hreg⟩ :=
      exists_intrinsicPredecessorRegular_in_open_fixedCell
        hQ p Nstar hJopen ⟨L₁, hL₁J⟩ hJcell
    have hLcell : L ∈ fixedCanonicalCutoffCell Q := hJcell hLJ
    have hbadL : ParityBad p L Kstar :=
      ⟨u, hune, humem, hJneg L hLJ⟩
    have hminL : ∀ M : ℕ, M < Kstar → ¬ AnyParityBad L M := by
      intro M hM
      exact not_anyParityBad_of_lt_cellMinimal hminCell hM hLcell
    exact ⟨Kstar, Nstar, L, p, hKtwo, hNstar, hsucc,
      hLcell, hbadL, hminL, hreg⟩
  · let p : ReversalParity := .odd
    obtain ⟨u, hune, humem, hneg⟩ := hbad
    obtain ⟨J, hJopen, hL₁J, hJcell, hJneg⟩ :=
      exists_open_fixedCell_negativeCanonicalSourceWitness_persistence
        Q Kstar hQ u hL₁cell hneg
    let Nstar := Kstar - 1
    have hNstar : 1 ≤ Nstar := by
      dsimp [Nstar]
      omega
    have hsucc : Nstar + 1 = Kstar := by
      dsimp [Nstar]
      omega
    obtain ⟨L, hLJ, hreg⟩ :=
      exists_intrinsicPredecessorRegular_in_open_fixedCell
        hQ p Nstar hJopen ⟨L₁, hL₁J⟩ hJcell
    have hLcell : L ∈ fixedCanonicalCutoffCell Q := hJcell hLJ
    have hbadL : ParityBad p L Kstar :=
      ⟨u, hune, humem, hJneg L hLJ⟩
    have hminL : ∀ M : ℕ, M < Kstar → ¬ AnyParityBad L M := by
      intro M hM
      exact not_anyParityBad_of_lt_cellMinimal hminCell hM hLcell
    exact ⟨Kstar, Nstar, L, p, hKtwo, hNstar, hsucc,
      hLcell, hbadL, hminL, hreg⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.exists_least_cellAnyParityBad_two_le
#print axioms Zeta23.CCM.not_anyParityBad_of_lt_cellMinimal
#print axioms Zeta23.CCM.exists_regular_cellMinimal_firstBad
