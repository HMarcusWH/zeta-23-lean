import Zeta23.CCM.CellMinimalRegularFirstBad

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4R7: bi-regular cell-minimal first bad

Dense regularity is available independently in each reversal parity.  Regularity
at one aperture is also locally persistent inside a fixed cutoff cell.  This
module composes those two facts with the already-proved persistence of one
strict negative first-bad witness.

The result strengthens the retained first-bad construction: the same aperture
can be chosen with both even and odd intrinsic predecessor blocks regular.

No successor branch is excluded, no arithmetic sign theorem is introduced,
and no negative-root, finite-to-infinite, or RH claim is made here.
-/

/-- Every nonempty open interval inside one fixed physical cutoff cell contains
an aperture where both reversal-parity predecessor blocks are regular at the
same predecessor size. -/
theorem exists_both_intrinsicPredecessorRegular_in_open_fixedCell
    {Q : ℕ} (hQ : 1 ≤ Q)
    (N : ℕ)
    {J : Set ℝ}
    (hJopen : IsOpen J)
    (hJne : J.Nonempty)
    (hJcell : J ⊆ fixedCanonicalCutoffCell Q) :
    ∃ L ∈ J,
      IntrinsicPredecessorRegular .even L N ∧
      IntrinsicPredecessorRegular .odd L N := by
  obtain ⟨Le, hLeJ, hregEven⟩ :=
    exists_intrinsicPredecessorRegular_in_open_fixedCell
      hQ .even N hJopen hJne hJcell
  have hLeCell : Le ∈ fixedCanonicalCutoffCell Q := hJcell hLeJ
  obtain ⟨U, hUopen, hLeU, hUcell, hregEvenU⟩ :=
    exists_open_fixedCell_intrinsicPredecessorRegular_persistence
      hQ .even N hLeCell hregEven
  let J' : Set ℝ := J ∩ U
  have hJ'open : IsOpen J' := hJopen.inter hUopen
  have hJ'ne : J'.Nonempty := ⟨Le, hLeJ, hLeU⟩
  have hJ'cell : J' ⊆ fixedCanonicalCutoffCell Q := by
    intro L hL
    exact hUcell hL.2
  obtain ⟨L, hLJ', hregOdd⟩ :=
    exists_intrinsicPredecessorRegular_in_open_fixedCell
      hQ .odd N hJ'open hJ'ne hJ'cell
  exact ⟨L, hLJ'.1, hregEvenU L hLJ'.2, hregOdd⟩

/-- Strengthened retained first-bad state: all historical first-bad ancestry is
kept, while both parity predecessor blocks are regular at the same aperture. -/
structure BiRegularCellMinimalFirstBadCertificate (Q : ℕ) where
  firstBad : RegularCellMinimalFirstBadCertificate Q
  regular_even :
    IntrinsicPredecessorRegular .even firstBad.L firstBad.Nstar
  regular_odd :
    IntrinsicPredecessorRegular .odd firstBad.L firstBad.Nstar

/-- A cell containing any parity-bad size admits a cell-minimal first-bad
certificate at an aperture where both predecessor parities are regular.  The
same strict negative witness is preserved while the aperture is moved. -/
theorem exists_biRegular_cellMinimal_firstBadCertificate
    (Q : ℕ) (hQ : 1 ≤ Q)
    (hex : ∃ K : ℕ, CellAnyParityBad Q K) :
    Nonempty (BiRegularCellMinimalFirstBadCertificate Q) := by
  obtain ⟨c⟩ := exists_regular_cellMinimal_firstBadCertificate Q hQ hex
  obtain ⟨u, hune, humem, hneg⟩ := c.bad
  obtain ⟨J, hJopen, hLJ, hJcell, hJneg⟩ :=
    exists_open_fixedCell_negativeCanonicalSourceWitness_persistence
      Q c.Kstar hQ u c.L_mem hneg
  obtain ⟨L, hLJ', hregEven, hregOdd⟩ :=
    exists_both_intrinsicPredecessorRegular_in_open_fixedCell
      hQ c.Nstar hJopen ⟨c.L, hLJ⟩ hJcell
  have hLcell : L ∈ fixedCanonicalCutoffCell Q := hJcell hLJ'
  have hbadL : ParityBad c.p L c.Kstar :=
    ⟨u, hune, humem, hJneg L hLJ'⟩
  have hsmaller :
      ∀ M : ℕ, M < c.Kstar → ¬ AnyParityBad L M := by
    intro M hM
    exact not_anyParityBad_of_lt_cellMinimal c.cell_minimal hM hLcell
  have hregSelected : IntrinsicPredecessorRegular c.p L c.Nstar := by
    cases hp : c.p with
    | even =>
        simpa [hp] using hregEven
    | odd =>
        simpa [hp] using hregOdd
  let c' : RegularCellMinimalFirstBadCertificate Q := {
    Kstar := c.Kstar
    Nstar := c.Nstar
    L := L
    p := c.p
    one_le_Q := c.one_le_Q
    two_le_Kstar := c.two_le_Kstar
    one_le_Nstar := c.one_le_Nstar
    succ_eq := c.succ_eq
    L_mem := hLcell
    bad := hbadL
    cell_minimal := c.cell_minimal
    smaller_good := hsmaller
    regular := hregSelected
  }
  exact ⟨{
    firstBad := c'
    regular_even := by simpa [c'] using hregEven
    regular_odd := by simpa [c'] using hregOdd
  }⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.exists_both_intrinsicPredecessorRegular_in_open_fixedCell
#print axioms Zeta23.CCM.BiRegularCellMinimalFirstBadCertificate
#print axioms Zeta23.CCM.exists_biRegular_cellMinimal_firstBadCertificate
