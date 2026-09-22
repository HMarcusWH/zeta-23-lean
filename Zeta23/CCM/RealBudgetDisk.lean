import Mathlib

noncomputable section

namespace Zeta23.CCM

/-!
# Real budget/disk geometry

Small ordered-real lemmas used after the retained canonical source has been
proved conjugation-fixed.  These statements are generic algebra: they carry no
CCM, zeta, first-bad, or RH authority by themselves.
-/

/-- A positive scalar budget and a disk trapped inside the positive shell
radius force the source scalar to be positive. -/
theorem realBudgetDisk_source_pos
    {B s f q R : ℝ}
    (hB : 0 < B)
    (hbudget : B ≤ s * f)
    (hq : 0 < q)
    (hdisk : (q - f) ^ 2 ≤ R)
    (hR : R ≤ q ^ 2) :
    0 < s := by
  have hsf : 0 < s * f := lt_of_lt_of_le hB hbudget
  have hsne : s ≠ 0 := by
    intro hs
    rw [hs, zero_mul] at hsf
    exact lt_irrefl 0 hsf
  by_contra hspos
  have hsle : s ≤ 0 := le_of_not_gt hspos
  have hsneg : s < 0 := lt_of_le_of_ne hsle hsne
  have hfneg : f < 0 := by
    rcases (mul_pos_iff.mp hsf) with hpp | hnn
    · exact False.elim ((not_lt_of_ge hsle) hpp.1)
    · exact hnn.2
  have hqdiff : q < q - f := by
    linarith
  have hqdiffpos : 0 < q - f := lt_trans hq hqdiff
  have hsquare : q ^ 2 < (q - f) ^ 2 := by
    nlinarith
  nlinarith

/-- Under the same hypotheses, once the source scalar is positive the completed
source scalar is positive as well. -/
theorem realBudgetDisk_completed_pos
    {B s f : ℝ}
    (hB : 0 < B)
    (hbudget : B ≤ s * f)
    (hs : 0 < s) :
    0 < f := by
  have hsf : 0 < s * f := lt_of_lt_of_le hB hbudget
  by_contra hfpos
  have hfle : f ≤ 0 := le_of_not_gt hfpos
  have hmul : s * f ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hs) hfle
  linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.realBudgetDisk_source_pos
#print axioms Zeta23.CCM.realBudgetDisk_completed_pos
