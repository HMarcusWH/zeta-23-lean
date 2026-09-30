import Zeta23.CCM.CanonicalGroundContinuity
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace Zeta23.CCM

open Set

/-!
# Post-#277 fixed-N zero-contact extraction

This module is pure finite-dimensional/topological infrastructure.  It consumes
fixed-N continuity together with a positive small-aperture anchor and a later
negative value, and returns an exact zero of the same legal successor ground.

The stronger first-negative-boundary package (nonnegative prefix plus outgoing
negative approach) is intentionally not faked here; it remains the next
refinement after the production continuity gate is discharged.
-/

/-- One exact fixed-N legal-ground zero contact bracketed by the quantitative
small-aperture base and a later negative endpoint. -/
structure GlobalParityBottomZeroContact where
  N : ℕ
  one_le_N : 1 ≤ N
  Lsmall : ℝ
  Lstar : ℝ
  Lneg : ℝ
  Lsmall_pos : 0 < Lsmall
  Lsmall_le_smallAperture : Lsmall ≤ (1 : ℝ) / 512
  Lsmall_lt_Lstar : Lsmall < Lstar
  Lstar_lt_Lneg : Lstar < Lneg
  base_positive :
    1 ≤ globalParitySuccessorBottom Lsmall N
  contact_zero :
    globalParitySuccessorBottom Lstar N = 0
  negative_endpoint :
    globalParitySuccessorBottom Lneg N < 0

/-- Fixed-N sign opposition plus the exact continuity interface forces a
genuine zero contact at the same finite successor index. -/
theorem exists_globalParityBottomZeroContact_of_signOpposition
    (hcont : CanonicalFixedNGroundContinuity)
    {N : ℕ} (hN : 1 ≤ N)
    {Lsmall Lneg : ℝ}
    (hLsmall : 0 < Lsmall)
    (hsmall : Lsmall ≤ (1 : ℝ) / 512)
    (hLt : Lsmall < Lneg)
    (hbase : 1 ≤ globalParitySuccessorBottom Lsmall N)
    (hneg : globalParitySuccessorBottom Lneg N < 0) :
    ∃ c : GlobalParityBottomZeroContact,
      c.N = N ∧ c.Lsmall = Lsmall ∧ c.Lneg = Lneg := by
  let g : ℝ → ℝ := fun L => globalParitySuccessorBottom L N
  have hsub : Icc Lsmall Lneg ⊆ Ioi (0 : ℝ) := by
    intro L hL
    exact lt_of_lt_of_le hLsmall hL.1
  have hcontIcc : ContinuousOn g (Icc Lsmall Lneg) :=
    (hcont N hN).mono hsub
  have hzeroMem : (0 : ℝ) ∈ Icc (g Lneg) (g Lsmall) := by
    constructor
    · exact le_of_lt hneg
    · exact le_trans (by norm_num) hbase
  have himage :
      (0 : ℝ) ∈ g '' Icc Lsmall Lneg :=
    intermediate_value_Icc' (le_of_lt hLt) hcontIcc hzeroMem
  obtain ⟨Lstar, hLstar, hzero⟩ := himage
  have hleft : Lsmall < Lstar := by
    rcases lt_or_eq_of_le hLstar.1 with h | h
    · exact h
    · subst Lstar
      have hz : globalParitySuccessorBottom Lsmall N = 0 := by
        simpa [g] using hzero
      linarith
  have hright : Lstar < Lneg := by
    rcases lt_or_eq_of_le hLstar.2 with h | h
    · exact h
    · subst Lstar
      have hz : globalParitySuccessorBottom Lneg N = 0 := by
        simpa [g] using hzero
      linarith
  let c : GlobalParityBottomZeroContact := {
    N := N
    one_le_N := hN
    Lsmall := Lsmall
    Lstar := Lstar
    Lneg := Lneg
    Lsmall_pos := hLsmall
    Lsmall_le_smallAperture := hsmall
    Lsmall_lt_Lstar := hleft
    Lstar_lt_Lneg := hright
    base_positive := hbase
    contact_zero := by simpa [g] using hzero
    negative_endpoint := hneg
  }
  exact ⟨c, rfl, rfl, rfl⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.exists_globalParityBottomZeroContact_of_signOpposition
